#include "F4SE/F4SE.h"
#include "RE/Fallout.h"
#include <REX/REX.h>
#include <Windows.h>
#include <atomic>
#include <chrono>
#include <cstring>
#include <cstdio>
#undef ERROR

// ============================================================================
// ExamineLagFix
//
// Removes the synchronous stall when the pickup-examine menu (ExamineMenu)
// opens for the first legendary weapon / magazine / featured item.
//
// Root causes (all synchronous, all before the menu's first visible frame):
//
//  A) SetUpExamineMenu rebuilds scrappableItemsMap on every menu open by
//     scanning the entire COBJ form array (formArrays[kCOBJ]) and running a
//     keyword check per recipe. The map's only consumer is
//     BuildWeaponScrappingArray, which the pickup-examine flow never calls
//     unless the player actually scraps the item - so the whole scan is
//     wasted work 99% of the time.
//
//  B) For weapons/armor the mod chain (BuildPossibleModList) re-evaluates
//     every COBJ recipe (attach point match + condition tree + CanBeUsedOn)
//     to build an installable-mod list that inspect mode never shows.
//     The "currently attached mods" preview comes from FindWeaponMods via
//     the instance data instead and is left untouched.
//
// Fix A: hook SetUpExamineMenu and temporarily zero the COBJ array size for
//   the duration of the original call (same store pattern CraftingMenuFix
//   proved safe for concurrent readers) - the scan loop runs zero iterations.
//   BuildWeaponScrappingArray is hooked to lazily rebuild the map (through
//   the vanilla predicate, replicated with CommonLib APIs) right before the
//   engine reads it, so scrapping still works identically. The scrappable
//   keyword comes from the engine's .data global (the one the vanilla scan
//   itself reads); GetFormByEditorID does not resolve at runtime.
//
// Fix B: vtable hook on BuildPossibleModList (slot 0x20, same slot
//   CraftingMenuFix uses - the two chain cleanly when both are installed).
//   In inspect mode the choice array is torn down exactly like the vanilla
//   prologue does and the scan is skipped; workbench mode runs vanilla.
//   The original function is resolved via the address library and verified
//   independently of the slot content, so a foreign vtable hook (other mods
//   do this) is detected and chained through instead of aborting.
//
// Fix C: vtable hook on UpdateItemList (slot 0x2F). The examine SWF is a
//   full workbench menu (mod select, item select, featured item) that also
//   has an inspect mode, and its AS3 init callback (IMenu::Call -> the
//   slot 0x39 initializer) unconditionally rebuilds the whole inventory
//   entry list on every open - visiting every carried item and pushing one
//   GFx object per entry into an entryList the inspect UI never displays.
//   With ~1800 distinct items that is well over a second of pure waste.
//
//   The catch: the displayed item itself rides on that list. The per-entry
//   loop (0xA18EF0) matches each entry against modItem/modStack and invokes
//   "selectedIndex" on the match - the inspect panel's name and model both
//   come from the selected entry, so the rebuild cannot simply be skipped
//   (skipping it makes the panel show an unrelated leftover item).
//
//   So instead the rebuild runs vanilla and the expensive parts are
//   filtered, in two layers that degrade into each other:
//   1. The per-entry callback UpdateItemList's walk loop calls directly
//      (entry patch, signature-located per runtime family) returns early
//      for entries whose id does not match modItem - skipping the GFx
//      invokes, the populate, and the entryList push for everything but
//      the examined item.
//   2. The slot 0x38 populate hook independently skips the per-entry GFx
//      object build (descriptor + eight member writes) for non-matching
//      entries, covering the case where layer 1 failed to install.
//   Matching entries - normally just the one - run the full vanilla path,
//   the selectedIndex invoke still fires on the real match, and the walk
//   keeps going (the callback contract returns "keep walking").
//
// All targets are resolved by signature / prologue verification with a
// hard fail-safe: any mismatch leaves that hook uninstalled (vanilla
// behavior). No hardcoded RVAs.
// ============================================================================

namespace
{
    // ------------------------------------------------------------------ //

    using SetUpExamineMenu_t = void (*)(RE::ExamineMenu*);
    using BuildWeaponScrappingArray_t = void (*)(RE::ExamineMenu*);
    using BuildPossibleModList_t = void (*)(RE::ExamineMenu*, RE::TESBoundObject*);
    // Fix C taps forward full 64-bit argument lanes on purpose. NG984's slot
    // 0x38 second parameter is a POINTER (engine passes &stackLocal, see the
    // mov eax,[rdx] prologue at 0xA12430) while the header declares a
    // by-value ObjectRefHandle - a typed forward truncated the caller's
    // pointer to 32 bits and crashed pickup. Same idea for the int tap:
    // forward the whole register so any real signature survives.
    using UpdateItemList_t = void (*)(RE::ExamineMenu*, std::uint64_t);
    using PopulateItemObj_t = void (*)(RE::ExamineMenu*, void*, const void*, void*);

    SetUpExamineMenu_t          g_origSetUp = nullptr;
    BuildWeaponScrappingArray_t g_origBWSA = nullptr;
    REL::Relocation<void (*)(RE::ExamineMenu*, RE::TESBoundObject*)> g_origBPML;

    REL::Relocation<UpdateItemList_t> g_origUpdateItemList;
    REL::Relocation<PopulateItemObj_t> g_origPopulate;

    // The engine caches the scrappable keyword in a .data global that the
    // vanilla scan reads directly. IDs: OG 515680, NG 2692427, AE 4799719.
    REL::Relocation<RE::BGSKeyword*> g_scrappableKwGlobal{ REL::VariantID(515680, 2692427, 4799719) };
    RE::BGSKeyword* g_scrappableKw = nullptr;

    // Fix C selective-populate state: active only while an inspect-mode
    // UpdateItemList is running. Plain stores/loads are fine - the list
    // build is single-threaded on the UI thread - but atomics keep the
    // populate hook's read honest under TSAN-style tooling.
    std::atomic<bool>        g_selectivePop{ false };
    std::uint32_t            g_popTargetId{ 0 };   // ExamineMenu::modItem.id
    std::atomic<std::uint32_t> g_popKept{ 0 };     // entries fully populated
    std::atomic<std::uint32_t> g_popSkipped{ 0 };  // entries skipped at populate

    // Second filter layer: the per-entry callback UpdateItemList's loop
    // calls directly (not a virtual - needs an entry patch). Skipping it for
    // non-target entries also skips the per-entry GFx invokes and the
    // entryList push, on top of what the populate filter already saves.
    using PerEntryFn = int (*)(void*, void*);  // (ctx, entry) -> keep walking
    PerEntryFn g_origPerEntry = nullptr;
    std::atomic<std::uint32_t> g_entrySkip{ 0 };

    // The examined entry's absolute index in the native entry array. The
    // displayed item is ultimately picked by reading "selectedIndex" back
    // off the SWF list object (FUN_140a0daa0) and indexing the native array
    // with it (CreateModdedInventoryItem). With the SWF list filtered to a
    // single entry that read comes back clamped, so GetSelectedIndex is
    // hooked to answer with this recorded index while it is valid.
    std::atomic<std::int32_t> g_targetIndex{ -1 };
    RE::ExamineMenu* g_targetMenu = nullptr;

    // FUN_140a0daa0: int GetSelectedIndex(ExamineMenu*) - reads the SWF-side
    // "selectedIndex". Entry patch, NG/AE signature only (OG layout differs;
    // there the per-entry filter stays disabled and the populate filter
    // alone keeps the display correct).
    using GetSelIdxFn = std::int64_t (*)(RE::ExamineMenu*);
    GetSelIdxFn g_origGetSelIdx = nullptr;

    // TESDataHandler::formArrays entries, engine layout (byte-verified in the
    // SetUpExamineMenu scan on OG163/NG980/NG984/AE221/AE240): entry stride
    // 0x18, { data@0, capacity@8, size@0x10 }. CommonLib's BSTArray is 0x10
    // with size@0x0C, so the built-in formArrays[kCOBJ] indexing misses by
    // 0x478 bytes - the entry address MUST be hand-computed.
    struct FormArrayEntry {
        RE::TESForm**       data;      // +0x00
        std::uint32_t       capacity;  // +0x08
        std::uint32_t       pad0C;     // +0x0C
        std::uint32_t       size;      // +0x10
        std::uint32_t       pad14;     // +0x14
    };
    static_assert(sizeof(FormArrayEntry) == 0x18);

    [[nodiscard]] FormArrayEntry* GetCobjEntry()
    {
        auto* handler = RE::TESDataHandler::GetSingleton();
        if (!handler) return nullptr;
        constexpr std::size_t kFormArraysOff = 0x68;                 // TESDataHandler::formArrays
        constexpr std::size_t kStride = 0x18;                        // engine entry stride
        constexpr std::size_t kCOBJ = 143;                           // ENUM_FORM_ID::kCOBJ ordinal
        const auto base = reinterpret_cast<std::uintptr_t>(handler) + kFormArraysOff;
        return reinterpret_cast<FormArrayEntry*>(base + kStride * kCOBJ);  // handler+0xDD0
    }

    // ------------------------------------------------------------------ //
    // Fix A: lazy rebuild of scrappableItemsMap
    // ------------------------------------------------------------------ //

    // Vanilla predicate (SetUpExamineMenu scan lambda, byte-verified against
    // OG/NG/AE): COBJ is not deleted, its createdItem exists and is a FLST
    // (batch scrapping recipe covering a weapon list), and the recipe's
    // filter keywords contain WorkbenchScrappableKeyword. Map layout:
    // key = FLST formID, value = COBJ formID (hash input is the key, as seen
    // in the vanilla lambda; BuildWeaponScrappingArray walks the FLST forms
    // to find the selected weapon and reads the COBJ for the component list).
    void LazyFillScrappables(RE::ExamineMenu* a_menu)
    {
        if (!g_scrappableKw) {
            g_scrappableKw = *reinterpret_cast<RE::BGSKeyword**>(g_scrappableKwGlobal.address());
        }
        if (!g_scrappableKw) return;  // vanilla with a null keyword inserts nothing either
        auto* handler = RE::TESDataHandler::GetSingleton();
        if (!handler) return;

        auto* cobjE = GetCobjEntry();
        if (!cobjE || !cobjE->data) return;

        auto& map = a_menu->scrappableItemsMap;
        for (std::uint32_t i = 0; i < cobjE->size; ++i) {
            auto* form = cobjE->data[i];
            auto* cobj = form ? form->As<RE::BGSConstructibleObject>() : nullptr;
            if (!cobj) continue;
            if (cobj->GetFormFlags() & 0x20) continue;  // deleted, same bit the vanilla lambda tests
            auto* created = cobj->createdItem;
            if (!created) continue;
            if (created->GetFormType() != RE::ENUM_FORM_ID::kFLST) continue;
            if (!cobj->filterKeywords.HasKeyword(g_scrappableKw)) continue;
            map.insert(
                RE::BSTTuple<const std::uint32_t, std::uint32_t>(
                    created->GetFormID(), cobj->GetFormID()));
        }
    }

    void HookedBuildWeaponScrappingArray(RE::ExamineMenu* a_menu)
    {
        if (a_menu && a_menu->scrappableItemsMap.size() == 0) {
            LazyFillScrappables(a_menu);
        }
        g_origBWSA(a_menu);
    }

    // During SetUpExamineMenu the COBJ array size is zeroed so the vanilla
    // scan loop runs zero iterations. Store ordering matches the "size=0
    // barrier" pattern CraftingMenuFix validated for concurrent readers:
    // data is never touched, only the size field flips, so any reader either
    // sees the old size or zero - both consistent states.
    void HookedSetUpExamineMenu(RE::ExamineMenu* a_menu)
    {
        auto* cobjE = GetCobjEntry();
        const std::uint32_t saved = cobjE ? cobjE->size : 0;
        if (cobjE && saved) {
            std::atomic_ref(cobjE->size).store(0, std::memory_order_release);
        }
        g_origSetUp(a_menu);
        if (cobjE && saved) {
            std::atomic_ref(cobjE->size).store(saved, std::memory_order_release);
        }
    }

    // ------------------------------------------------------------------ //
    // Fix B: skip BuildPossibleModList in inspect mode
    // ------------------------------------------------------------------ //

    void HookedBuildPossibleModList(RE::ExamineMenu* a_menu, RE::TESBoundObject* a_object)
    {
        if (a_menu && a_menu->inspectMode) {
            // Mirror the vanilla prologue teardown so the menu is left in the
            // exact "no choices" state: destroy every ModChoiceData (drops the
            // required-perk arrays), reset the count, clear the null mod.
            // The buffer itself is left allocated; the vanilla function
            // deallocates it on its next real run.
            auto& arr = a_menu->modChoiceArray;
            for (std::uint32_t i = 0; i < arr.size(); ++i) {
                std::destroy_at(&arr[i]);
            }
            arr.clear();
            a_menu->nullMod = nullptr;
            return;
        }
        g_origBPML(a_menu, a_object);
    }

    // ------------------------------------------------------------------ //
    // Install helpers
    // ------------------------------------------------------------------ //

    // JMP14 entry hook (InventoryLagFix pattern): save the prologue, build a
    // trampoline stub (prologue + jmp back), write a jmp to the hook over the
    // prologue. The displaced prologue must be at least JMP14-sized and end
    // on an instruction boundary - both verified per target below.
    std::uintptr_t PatchFuncEntry(std::uintptr_t a_addr, std::size_t a_hookSize,
        void* a_hookFn, const char* a_tag)
    {
        if (a_hookSize < sizeof(REL::ASM::JMP14)) {
            REX::ERROR("ExamineLagFix: [{}] displacement {} < JMP14 size {}, hook NOT installed",
                a_tag, a_hookSize, sizeof(REL::ASM::JMP14));
            return 0;
        }

        std::byte saved[32];
        std::memcpy(saved, reinterpret_cast<const void*>(a_addr), a_hookSize);

        auto& tramp = REL::GetTrampoline();
        auto* stub = static_cast<std::byte*>(tramp.allocate(a_hookSize + sizeof(REL::ASM::JMP14)));
        if (!stub) {
            REX::ERROR("ExamineLagFix: [{}] trampoline alloc failed", a_tag);
            return 0;
        }
        std::memcpy(stub, saved, a_hookSize);
        REL::ASM::JMP14 jmpBack(a_addr + a_hookSize);
        std::memcpy(stub + a_hookSize, &jmpBack, sizeof(jmpBack));

        REL::ASM::JMP14 jmpHook(reinterpret_cast<std::uintptr_t>(a_hookFn));
        REL::WriteSafe(a_addr, reinterpret_cast<const std::byte*>(&jmpHook), sizeof(jmpHook));

        if (std::memcmp(reinterpret_cast<const void*>(a_addr), &jmpHook, sizeof(jmpHook)) != 0) {
            REL::WriteSafe(a_addr, saved, a_hookSize);
            REX::ERROR("ExamineLagFix: [{}] patch readback MISMATCH @ 0x{:X}, restored", a_tag, a_addr);
            return 0;
        }
        std::atomic_thread_fence(std::memory_order_seq_cst);
        return reinterpret_cast<std::uintptr_t>(stub);
    }

    // Scan the executing module's .text for a byte pattern; returns the only
    // match or 0 (same search style as CraftingMenuFix's GetKeywordByIndex
    // scan - zero hardcoded RVAs, unique-match-or-bail).
    std::uintptr_t ScanTextUnique(const std::uint8_t* a_sig, std::size_t a_len, const char* a_tag)
    {
        const auto base = reinterpret_cast<std::uintptr_t>(GetModuleHandleW(nullptr));
        if (!base) return 0;
        auto* dos = reinterpret_cast<IMAGE_DOS_HEADER*>(base);
        if (dos->e_magic != IMAGE_DOS_SIGNATURE) return 0;
        auto* nt = reinterpret_cast<IMAGE_NT_HEADERS*>(base + dos->e_lfanew);
        if (nt->Signature != IMAGE_NT_SIGNATURE) return 0;
        auto* sec = IMAGE_FIRST_SECTION(nt);
        for (std::uint32_t i = 0; i < nt->FileHeader.NumberOfSections; ++i, ++sec) {
            if (std::memcmp(sec->Name, ".text", 6) != 0) continue;
            const auto* begin = reinterpret_cast<const std::uint8_t*>(base + sec->VirtualAddress);
            const auto* end = begin + sec->Misc.VirtualSize;
            std::uintptr_t found = 0;
            int matches = 0;
            const auto* p = begin;
            while (p < end &&
                   (p = reinterpret_cast<const std::uint8_t*>(
                        std::memchr(p, a_sig[0], static_cast<std::size_t>(end - p)))) != nullptr) {
                if (end - p >= static_cast<std::ptrdiff_t>(a_len) &&
                    std::memcmp(p, a_sig, a_len) == 0) {
                    ++matches;
                    found = base + sec->VirtualAddress + (p - begin);
                    if (matches > 1) break;
                }
                ++p;
            }
            if (matches != 1) {
                REX::ERROR("ExamineLagFix: [{}] signature matches={} (need exactly 1)", a_tag, matches);
                return 0;
            }
            return found;
        }
        return 0;
    }

    // Walk back from a hit to the function start (int3 padding). The three
    // runtime families place the OR opcode 0xA..0xF bytes into the function.
    [[nodiscard]] std::uintptr_t FuncStartFromHit(std::uintptr_t a_hit, std::size_t a_back)
    {
        auto* p = reinterpret_cast<const std::uint8_t*>(a_hit);
        for (std::size_t i = 0; i < a_back; ++i) {
            if (*(p - 1) == 0xCC) return a_hit - i;
            --p;
        }
        return 0;
    }

    bool VerifyBytes(std::uintptr_t a_addr, const std::uint8_t* a_expected, std::size_t a_len)
    {
        return std::memcmp(reinterpret_cast<const void*>(a_addr), a_expected, a_len) == 0;
    }

    // Timing helper for the examine-menu measurements below. The weapon-switch
    // side of this hunt now lives in its own plugin - see WeaponSwapLagFix.
    [[nodiscard]] std::int64_t NowUs()
    {
        return std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now().time_since_epoch()).count();
    }

    // ------------------------------------------------------------------ //

    bool InstallFixA()
    {
        // The scrappable keyword is read from the engine's .data global - the
        // exact pointer the vanilla scan compares against (GetFormByEditorID
        // does not resolve at runtime). A null global only downgrades the lazy
        // fill to a no-op, which matches vanilla's behavior with a null
        // keyword (its scan also inserts nothing), so the hooks install
        // regardless and LazyFill re-reads the global at call time.
        g_scrappableKw = *reinterpret_cast<RE::BGSKeyword**>(g_scrappableKwGlobal.address());
        if (g_scrappableKw && g_scrappableKw->GetFormType() != RE::ENUM_FORM_ID::kKYWD) {
            REX::ERROR("ExamineLagFix: scrappable keyword global resolved to form type 0x{:X}, ignoring",
                std::to_underlying(g_scrappableKw->GetFormType()));
            g_scrappableKw = nullptr;
        }
        if (g_scrappableKw) {
            REX::INFO("ExamineLagFix: scrappable keyword 0x{:08X} resolved from engine global",
                g_scrappableKw->GetFormID());
        } else {
            REX::ERROR("ExamineLagFix: scrappable keyword global is null, lazy fill will no-op");
        }

        // ---- locate SetUpExamineMenu ----
        // OR dword ptr [RCX+0x58], 0xA500 - unique in .text on OG163/NG980/
        // NG984/AE221/AE240 (offline-verified). The opcode lands 0xA..0xF
        // bytes into the function; walk back to the int3 padding.
        static constexpr std::uint8_t kOrSig[] = { 0x81, 0x49, 0x58, 0x00, 0xA5, 0x00, 0x00 };
        const auto orHit = ScanTextUnique(kOrSig, sizeof(kOrSig), "SetUpExamineMenu");
        if (!orHit) return false;
        const auto setUp = FuncStartFromHit(orHit, 0x40);
        if (!setUp) {
            REX::ERROR("ExamineLagFix: SetUpExamineMenu start not found before hit 0x{:X}", orHit);
            return false;
        }

        // Family prologues (offline-verified; hook sizes land on instruction
        // boundaries and contain no RIP-relative encodings).
        // OG163 : mov [rsp+0x20],rbx; push rbp; sub rsp,0x60; or [rcx+0x58],0xA500
        static constexpr std::uint8_t kProOG[]{
            0x48, 0x89, 0x5C, 0x24, 0x20, 0x55, 0x48, 0x83, 0xEC, 0x60,
            0x81, 0x49, 0x58, 0x00, 0xA5, 0x00, 0x00 };
        constexpr std::size_t kHookOG = 17;
        // NG980/984 : push rbx/rsi/rdi/r12/r14/r15; sub rsp,0x60; or ...
        static constexpr std::uint8_t kProNG[]{
            0x40, 0x53, 0x56, 0x57, 0x41, 0x54, 0x41, 0x56, 0x48, 0x83, 0xEC, 0x60,
            0x81, 0x49, 0x58, 0x00, 0xA5, 0x00, 0x00, 0x4C, 0x8B, 0xF1 };
        constexpr std::size_t kHookNG = 22;
        // AE221/240 : push rbx/rsi/rdi/r12/r14/r15; sub rsp,0x80; or ...
        static constexpr std::uint8_t kProAE[]{
            0x40, 0x53, 0x56, 0x57, 0x41, 0x54, 0x41, 0x56, 0x48, 0x81, 0xEC, 0x80, 0x00, 0x00, 0x00,
            0x81, 0x49, 0x58, 0x00, 0xA5, 0x00, 0x00, 0x4C, 0x8B, 0xF1 };
        constexpr std::size_t kHookAE = 25;

        std::size_t hookSize = 0;
        const char* family = nullptr;
        if (VerifyBytes(setUp, kProOG, sizeof(kProOG))) {
            hookSize = kHookOG; family = "OG";
        } else if (VerifyBytes(setUp, kProNG, sizeof(kProNG))) {
            hookSize = kHookNG; family = "NG";
        } else if (VerifyBytes(setUp, kProAE, sizeof(kProAE))) {
            hookSize = kHookAE; family = "AE";
        } else {
            REX::ERROR("ExamineLagFix: SetUpExamineMenu prologue mismatch @ 0x{:X}, Fix A NOT installed", setUp);
            return false;
        }

        const auto setUpStub = PatchFuncEntry(setUp, hookSize, &HookedSetUpExamineMenu, "SetUpExamineMenu");
        if (!setUpStub) return false;
        g_origSetUp = reinterpret_cast<SetUpExamineMenu_t>(setUpStub);
        REX::INFO("ExamineLagFix: SetUpExamineMenu hooked @ 0x{:X} ({} family, {} bytes)",
            setUp, family, hookSize);

        // ---- locate BuildWeaponScrappingArray (address library ID) ----
        REL::Relocation<BuildWeaponScrappingArray_t> bwsa{ RE::ID::ExamineMenu::BuildWeaponScrappingArray };
        const auto bwsaAddr = reinterpret_cast<std::uintptr_t>(bwsa.get());
        if (!bwsaAddr) {
            REX::ERROR("ExamineLagFix: BuildWeaponScrappingArray address resolve failed");
            return false;
        }
        // OG163 : mov rax,rsp; mov [rax+8],rcx; push rbp; push r13; lea rbp,[rax-0x5F]; sub rsp,0x98
        static constexpr std::uint8_t kBwsaOG[]{
            0x48, 0x8B, 0xC4, 0x48, 0x89, 0x48, 0x08, 0x55, 0x41, 0x55,
            0x48, 0x8D, 0x68, 0xA1, 0x48, 0x81, 0xEC, 0x98, 0x00, 0x00, 0x00 };
        constexpr std::size_t kBwsaHookOG = 21;
        // NG/AE : mov rax,rsp; mov [rax+8],rcx; push rbp; lea rbp,[rax-0x5F]; sub rsp,0x90
        static constexpr std::uint8_t kBwsaNG[]{
            0x48, 0x8B, 0xC4, 0x48, 0x89, 0x48, 0x08, 0x55,
            0x48, 0x8D, 0x68, 0xA1, 0x48, 0x81, 0xEC, 0x90, 0x00, 0x00, 0x00 };
        constexpr std::size_t kBwsaHookNG = 19;

        std::size_t bwsaHook = 0;
        if (VerifyBytes(bwsaAddr, kBwsaOG, sizeof(kBwsaOG))) {
            bwsaHook = kBwsaHookOG;
        } else if (VerifyBytes(bwsaAddr, kBwsaNG, sizeof(kBwsaNG))) {
            bwsaHook = kBwsaHookNG;
        } else {
            REX::ERROR("ExamineLagFix: BuildWeaponScrappingArray prologue mismatch @ 0x{:X}, Fix A NOT installed",
                bwsaAddr);
            return false;
        }

        const auto bwsaStub = PatchFuncEntry(bwsaAddr, bwsaHook, &HookedBuildWeaponScrappingArray, "BWSA");
        if (!bwsaStub) return false;
        g_origBWSA = reinterpret_cast<BuildWeaponScrappingArray_t>(bwsaStub);
        REX::INFO("ExamineLagFix: BuildWeaponScrappingArray hooked @ 0x{:X} ({} bytes)", bwsaAddr, bwsaHook);
        return true;
    }

    // ------------------------------------------------------------------ //

    [[nodiscard]] bool IsInsideExe(std::uintptr_t a_addr)
    {
        const auto base = reinterpret_cast<std::uintptr_t>(GetModuleHandleW(nullptr));
        if (!base || a_addr < base) return false;
        auto* dos = reinterpret_cast<IMAGE_DOS_HEADER*>(base);
        if (dos->e_magic != IMAGE_DOS_SIGNATURE) return false;
        auto* nt = reinterpret_cast<IMAGE_NT_HEADERS*>(base + dos->e_lfanew);
        if (nt->Signature != IMAGE_NT_SIGNATURE) return false;
        return a_addr < base + nt->OptionalHeader.SizeOfImage;
    }

    // Name the module that vtable-hooked a slot before us, so the log tells
    // the user exactly who else is in the chain.
    // void LogForeignHooker(std::uintptr_t a_target, const char* a_what)
    // {
    //     HMODULE mod = nullptr;
    //     if (!GetModuleHandleExW(
    //             GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,
    //             reinterpret_cast<LPCWSTR>(a_target), &mod) || !mod) {
    //         REX::INFO("ExamineLagFix: {} slot target 0x{:X} belongs to no module (raw memory)",
    //             a_what, a_target);
    //         return;
    //     }
    //     wchar_t wpath[MAX_PATH]{};
    //     GetModuleFileNameW(mod, wpath, MAX_PATH);
    //     const auto* wbase = std::wcsrchr(wpath, L'\\');
    //     char name[MAX_PATH]{};
    //     WideCharToMultiByte(CP_UTF8, 0, wbase ? wbase + 1 : wpath, -1,
    //         name, sizeof(name), nullptr, nullptr);
    //     REX::INFO("ExamineLagFix: {} slot already hooked by \"{}\", chaining on top", a_what, name);
    // }

    bool InstallFixB()
    {
        // Resolve the ORIGINAL BuildPossibleModList through the address
        // library (IDs: OG 1132407, NG/AE 2223025), independent of whatever
        // the vtable slot currently holds - other plugins vtable-hook this
        // slot before kGameDataReady (observed in the wild: slot pointed
        // outside Fallout4.exe and the old slot-content check bailed).
        REL::Relocation<std::uintptr_t> origBpml{ REL::VariantID(1132407, 2223025, 2223025) };
        const auto origAddr = origBpml.address();

        // Prologue verification runs against the RESOLVED original (OG family
        // and NG/AE family, same bytes CraftingMenuFix v8 verifies). A
        // mismatch means the ID is wrong for this runtime - stay vanilla.
        static constexpr std::uint8_t kPrologNG[] = {
            0x4c, 0x8b, 0xdc, 0x49, 0x89, 0x53, 0x10, 0x55,
            0x49, 0x8d, 0x6b, 0xa1, 0x48, 0x81, 0xec, 0xe0, 0x00, 0x00, 0x00 };
        static constexpr std::uint8_t kPrologOG[] = {
            0x48, 0x8b, 0xc4, 0x48, 0x89, 0x50, 0x10, 0x55,
            0x48, 0x8d, 0x68, 0xa1, 0x48, 0x81, 0xec, 0xf0, 0x00, 0x00, 0x00 };
        const auto* bytes = reinterpret_cast<const std::uint8_t*>(origAddr);
        const bool ok = std::memcmp(bytes, kPrologNG, sizeof(kPrologNG)) == 0 ||
                        std::memcmp(bytes, kPrologOG, sizeof(kPrologOG)) == 0;
        if (!ok) {
            char hex[128];
            int n = std::snprintf(hex, sizeof(hex), "BPML @ 0x%llX prologue: ",
                static_cast<unsigned long long>(origAddr));
            for (int i = 0; i < 19 && n < static_cast<int>(sizeof(hex)) - 4; ++i)
                n += std::snprintf(hex + n, sizeof(hex) - n, "%02X", bytes[i]);
            REX::ERROR("ExamineLagFix: {} - mismatch, Fix B NOT installed", hex);
            return false;
        }

        // Compare the live slot against the resolved original.
        REL::Relocation<std::uintptr_t> vtbl{ RE::VTABLE::ExamineMenu[0] };
        const auto* vtblPtr = reinterpret_cast<const std::uintptr_t*>(vtbl.address());
        const auto slotTarget = vtblPtr[0x20];

        if (slotTarget != origAddr) {
            if (IsInsideExe(slotTarget)) {
                // Slot points at a different function inside the exe: our
                // vtable or function ID is wrong for this runtime. Touch
                // nothing.
                REX::ERROR("ExamineLagFix: BPML slot 0x{:X} != resolved 0x{:X} (both in exe), "
                           "Fix B NOT installed", slotTarget, origAddr);
                return false;
            }
            // Foreign plugin hook. write_vfunc returns the current entry, so
            // our chain naturally calls it in workbench mode; in inspect mode
            // we skip the whole chain, which is the entire point of the fix.
            // LogForeignHooker(slotTarget, "BPML");
        }

        g_origBPML = vtbl.write_vfunc(0x20, &HookedBuildPossibleModList);
        REX::INFO("ExamineLagFix: BuildPossibleModList hooked via vtable slot 0x20 (original 0x{:X})",
            origAddr);
        return true;
    }

    // ------------------------------------------------------------------ //
    // Fix C: filter the inspect-mode entry-list rebuild down to the item
    // actually being examined (see the header comment for why the rebuild
    // itself must run).
    // ------------------------------------------------------------------ //

    void HookedPopulateInventoryItemObj(RE::ExamineMenu* a_menu, void* a_owner,
        const void* a_entry, void* a_itemObj);

    void HookedUpdateItemList(RE::ExamineMenu* a_menu, std::uint64_t a_idx)
    {
        // const auto t0 = NowUs();
        const bool selective = a_menu && a_menu->inspectMode;
        if (selective) {
            g_popTargetId = a_menu->modItem.id;
            g_popKept.store(0);
            g_popSkipped.store(0);
            g_entrySkip.store(0);
            g_selectivePop.store(true, std::memory_order_release);
        }
        g_origUpdateItemList(a_menu, a_idx);
        g_selectivePop.store(false, std::memory_order_release);
        // REX::INFO("ExamineLagFix DIAG: UpdateItemList inspect={} took {}us kept={} skipped={} entrySkip={}",
        //     selective, NowUs() - t0, g_popKept.load(), g_popSkipped.load(), g_entrySkip.load());
        if (selective) {
            const auto kept = g_popKept.load();
            if (kept != 0) {
                // Publish the examined entry's absolute index so the
                // GetSelectedIndex hook can answer CreateModdedInventoryItem
                // with it. The invoke re-asserts it on the SWF side as well -
                // RefreshList may have clamped it to the filtered list
                // length - but the hook is what actually feeds the display.
                const auto targetIdx = g_targetIndex.exchange(-1);
                if (targetIdx >= 0) {
                    g_targetIndex.store(targetIdx, std::memory_order_release);
                    g_targetMenu = a_menu;
                    Scaleform::GFx::Value args[1]{ Scaleform::GFx::Value{ targetIdx } };
                    a_menu->itemList.Invoke("selectedIndex", nullptr, args, 1);
                }
            } else {
                // Nothing matched modItem - either the item left the inventory
                // mid-open or the id read is off. Full vanilla next time.
                REX::ERROR("ExamineLagFix: inspect rebuild matched nothing "
                           "(target 0x{:08X}, {} entries) - display may be stale",
                    g_popTargetId, g_popSkipped.load() + g_entrySkip.load());
            }
        } else {
            // A non-inspect rebuild invalidates any recorded target index.
            g_targetIndex.store(-1, std::memory_order_release);
        }
    }

    std::int64_t HookedGetSelIdx(RE::ExamineMenu* a_menu)
    {
        const auto own = g_targetIndex.load(std::memory_order_acquire);
        if (own >= 0 && a_menu == g_targetMenu) {
            return own;
        }
        return g_origGetSelIdx(a_menu);
    }

    int HookedPerEntry(void* a_ctx, void* a_entry)
    {
        if (g_selectivePop.load(std::memory_order_acquire) && a_entry) {
            const auto entryId = *static_cast<const std::uint32_t*>(a_entry);
            if (entryId != g_popTargetId) {
                // The walk context (verified identical on OG163/NG984/AE221:
                // ctx+0x00 menu, ctx+0x08 selected-index slot, ctx+0x10 the
                // entry counter) matters more than it looks: on a match the
                // original stores the counter into the selectedIndex it
                // invokes, and the displayed item is then fetched by that
                // ABSOLUTE index into the native entry array - not by list
                // position. So a skipped entry must still bump the counter,
                // or the examine panel shows whatever sits at array index 0.
                ++*reinterpret_cast<std::int32_t*>(
                    *reinterpret_cast<void**>(static_cast<std::byte*>(a_ctx) + 0x10));
                g_entrySkip.fetch_add(1);
                return 1;  // vanilla always returns 1; 0 would abort the walk
            }
            // Target entry: capture its absolute index (the counter value
            // the vanilla match is about to invoke) for the post-rebuild
            // re-assert in HookedUpdateItemList.
            g_targetIndex.store(*reinterpret_cast<std::int32_t*>(
                *reinterpret_cast<void**>(static_cast<std::byte*>(a_ctx) + 0x10)));
        }
        return g_origPerEntry(a_ctx, a_entry);
    }

    // Scan .text for a signature, then keep only candidates whose
    // fixed-offset anchor bytes match - anchors let the check skip over
    // rip-relative / rel32 encodings that differ per build. Exactly one
    // survivor must remain or nothing is hooked. a_allowMiss silences the
    // zero-match case (used when trying one family's signature before
    // another's).
    struct SigAnchor { std::size_t off; const std::uint8_t* bytes; std::size_t len; };

    std::uintptr_t ScanTextSig(const std::uint8_t* a_sig, std::size_t a_len,
        const SigAnchor* a_anchors, std::size_t a_nAnchors,
        bool a_allowMiss, const char* a_tag)
    {
        const auto base = reinterpret_cast<std::uintptr_t>(GetModuleHandleW(nullptr));
        if (!base) return 0;
        auto* dos = reinterpret_cast<IMAGE_DOS_HEADER*>(base);
        if (dos->e_magic != IMAGE_DOS_SIGNATURE) return 0;
        auto* nt = reinterpret_cast<IMAGE_NT_HEADERS*>(base + dos->e_lfanew);
        if (nt->Signature != IMAGE_NT_SIGNATURE) return 0;
        auto* sec = IMAGE_FIRST_SECTION(nt);
        for (std::uint32_t i = 0; i < nt->FileHeader.NumberOfSections; ++i, ++sec) {
            if (std::memcmp(sec->Name, ".text", 6) != 0) continue;
            const auto* begin = reinterpret_cast<const std::uint8_t*>(base + sec->VirtualAddress);
            const auto* end = begin + sec->Misc.VirtualSize;
            std::uintptr_t found = 0;
            int survivors = 0;
            const auto* p = begin;
            while (p < end &&
                   (p = reinterpret_cast<const std::uint8_t*>(
                        std::memchr(p, a_sig[0], static_cast<std::size_t>(end - p)))) != nullptr) {
                if (end - p >= static_cast<std::ptrdiff_t>(a_len) &&
                    std::memcmp(p, a_sig, a_len) == 0) {
                    bool ok = true;
                    for (std::size_t a = 0; a < a_nAnchors && ok; ++a) {
                        const auto& an = a_anchors[a];
                        ok = (p + an.off + an.len <= end) &&
                             std::memcmp(p + an.off, an.bytes, an.len) == 0;
                    }
                    if (ok) {
                        ++survivors;
                        found = base + sec->VirtualAddress + (p - begin);
                        if (survivors > 1) break;
                    }
                }
                ++p;
            }
            if (survivors == 1) return found;
            if (survivors == 0 && a_allowMiss) return 0;
            REX::ERROR("ExamineLagFix: [{}] signature survivors={} (need exactly 1)",
                a_tag, survivors);
            return 0;
        }
        return 0;
    }

    bool InstallGetSelIdxHook()
    {
        // NG984/AE221/AE240 (offline-verified unique): push rbx; sub
        // rsp,0x50; mov rdx,[rcx+0x498]; lea r9,[rsp+0x30] - 18 clean
        // bytes, the rip-relative lea r8 only follows at +20. Anchors
        // verify the body (menu+0x490/+0x488 loads) past that encoding.
        static constexpr std::uint8_t kPro[]{
            0x40, 0x53, 0x48, 0x83, 0xEC, 0x50,
            0x48, 0x8B, 0x91, 0x98, 0x04, 0x00, 0x00,
            0x4C, 0x8D, 0x4C, 0x24, 0x30 };
        static constexpr std::uint8_t kA1[]{ 0x48, 0x89, 0x44, 0x24, 0x30, 0x89, 0x44, 0x24, 0x38 };
        static constexpr std::uint8_t kA2[]{ 0x8B, 0x81, 0x90, 0x04, 0x00, 0x00 };
        static constexpr std::uint8_t kA3[]{ 0x48, 0x8B, 0x89, 0x88, 0x04, 0x00, 0x00 };
        const SigAnchor anchors[] = {
            { 27, kA1, sizeof(kA1) },
            { 36, kA2, sizeof(kA2) },
            { 42, kA3, sizeof(kA3) },
        };
        const auto addr = ScanTextSig(kPro, sizeof(kPro), anchors, std::size(anchors),
            true, "GetSelIdx-NG/AE");
        if (!addr) {
            // OG builds this function differently; nothing gets patched.
            return false;
        }
        const auto stub = PatchFuncEntry(addr, sizeof(kPro), &HookedGetSelIdx, "GetSelIdx");
        if (!stub) return false;
        g_origGetSelIdx = reinterpret_cast<GetSelIdxFn>(stub);
        REX::INFO("ExamineLagFix: GetSelectedIndex hooked @ 0x{:X} (18 bytes)", addr);
        return true;
    }

    bool InstallPerEntryHook()
    {
        // NG984/AE221/AE240 (offline-verified unique in .text): push
        // rbp/rbx/rdi/r13; lea rbp,[rsp-0x3F]; sub rsp,0x88; mov rdi,rcx;
        // mov r13,rdx. The 18 displaced bytes contain no rip-relative
        // encodings and end on an instruction boundary.
        static constexpr std::uint8_t kProNG[]{
            0x40, 0x55, 0x53, 0x57, 0x41, 0x55,
            0x48, 0x8D, 0x6C, 0x24, 0xC1,
            0x48, 0x81, 0xEC, 0x88, 0x00, 0x00, 0x00,
            0x48, 0x8B, 0xF9, 0x4C, 0x8B, 0xEA };
        constexpr std::size_t kHookNG = 18;

        // OG163 (offline-verified unique with the anchors): push
        // rbp/rbx/rdi; mov rbp,rsp; sub rsp,0x70; mov rdi,rcx. The 14
        // displaced bytes are clean; the anchors verify the body past the
        // rip-relative loads this build uses.
        static constexpr std::uint8_t kProOG[]{
            0x40, 0x55, 0x53, 0x57,
            0x48, 0x8B, 0xEC, 0x48, 0x83, 0xEC, 0x70,
            0x48, 0x8B, 0xF9 };
        constexpr std::size_t kHookOG = 14;
        // +14 mov rcx,[rip+X] (7B skipped); +21 mov rbx,rdx; +24 call
        // (5B skipped); +29 mov [rbp+0x28],rax / test rax,rax; +36 jz
        // (disp skipped); +42 mov r9,[rdi]
        static constexpr std::uint8_t kA1[]{ 0x48, 0x8B, 0xDA };
        static constexpr std::uint8_t kA2[]{ 0x48, 0x89, 0x45, 0x28, 0x48, 0x85, 0xC0 };
        static constexpr std::uint8_t kA3[]{ 0x0F, 0x84 };
        static constexpr std::uint8_t kA4[]{ 0x4C, 0x8B, 0x0F };
        const SigAnchor ogAnchors[] = {
            { 21, kA1, sizeof(kA1) },
            { 29, kA2, sizeof(kA2) },
            { 36, kA3, sizeof(kA3) },
            { 42, kA4, sizeof(kA4) },
        };

        auto addr = ScanTextSig(kProNG, sizeof(kProNG), nullptr, 0, true, "PerEntry-NG/AE");
        std::size_t hookSize = kHookNG;
        const char* family = "NG/AE";
        if (!addr) {
            addr = ScanTextSig(kProOG, sizeof(kProOG), ogAnchors, std::size(ogAnchors),
                true, "PerEntry-OG");
            hookSize = kHookOG;
            family = "OG";
        }
        if (!addr) {
            REX::ERROR("ExamineLagFix: per-entry hook NOT installed (no unique match) "
                       "- populate filter still covers the expensive part");
            return false;
        }
        const auto stub = PatchFuncEntry(addr, hookSize, &HookedPerEntry, "PerEntry");
        if (!stub) return false;
        g_origPerEntry = reinterpret_cast<PerEntryFn>(stub);
        REX::INFO("ExamineLagFix: per-entry callback hooked @ 0x{:X} ({} family, {} bytes)",
            addr, family, hookSize);
        return true;
    }

    bool InstallFixC()
    {
        // No address-library ID exists for UpdateItemList or the populate
        // thunk; the slot layout itself is the identification (0x20 proved
        // identical on all three runtimes, and the 0x2F/0x38 entries land
        // on the list-rebuild functions the crash dump already walked). A
        // foreign vtable hook just chains - our decisions are mode- and
        // entry-based, not address-based.
        REL::Relocation<std::uintptr_t> vtbl{ RE::VTABLE::ExamineMenu[0] };
        const auto* vtblPtr = reinterpret_cast<const std::uintptr_t*>(vtbl.address());
        // if (!IsInsideExe(vtblPtr[0x2F])) {
        //     LogForeignHooker(vtblPtr[0x2F], "UpdateItemList");
        // }
        // if (!IsInsideExe(vtblPtr[0x38])) {
        //     LogForeignHooker(vtblPtr[0x38], "PopulateInventoryItemObj");
        // }
        g_origUpdateItemList = vtbl.write_vfunc(0x2F, &HookedUpdateItemList);
        g_origPopulate       = vtbl.write_vfunc(0x38, &HookedPopulateInventoryItemObj);
        REX::INFO("ExamineLagFix: UpdateItemList + populate hooked via vtable "
                  "slots 0x2F/0x38 (originals 0x{:X}/0x{:X})",
            vtblPtr[0x2F], vtblPtr[0x38]);
        // Second layer: entry-patch the per-entry callback so non-target
        // entries skip their GFx invokes and the entryList push too. It
        // depends on the GetSelectedIndex hook being live first - the skips
        // break the SWF-side selectedIndex the display path reads back, and
        // without the override the panel would show a leftover entry. Where
        // the override cannot be verified (OG layout differs) we stay on the
        // populate-only filter, which is slower but keeps the display right.
        if (InstallGetSelIdxHook()) {
            InstallPerEntryHook();
        } else {
            REX::ERROR("ExamineLagFix: GetSelectedIndex hook NOT installed - "
                       "per-entry filter disabled, populate filter only");
        }
        return true;
    }

    // ------------------------------------------------------------------ //
    // Fix C populate filter (layer 2): while an inspect-mode rebuild runs,
    // entries other than the examined item skip their GFx object build.
    // ------------------------------------------------------------------ //

    void HookedPopulateInventoryItemObj(RE::ExamineMenu* a_menu, void* a_owner,
        const void* a_entry, void* a_itemObj)
    {
        if (g_selectivePop.load(std::memory_order_acquire)) {
            // Inspect-mode list rebuild in flight: only the entry matching
            // the examined item needs its GFx object - the rest land in the
            // hidden entryList as unread placeholders. The entry's first
            // field is the item id the engine's own match (0xA18EF0)
            // compares against modItem.
            const auto entryId = a_entry
                ? *static_cast<const std::uint32_t*>(a_entry)
                : 0;
            if (entryId != g_popTargetId) {
                g_popSkipped.fetch_add(1);
                return;
            }
            g_popKept.fetch_add(1);
        }
        g_origPopulate(a_menu, a_owner, a_entry, a_itemObj);
    }
}


F4SE_PLUGIN_QUERY(const F4SE::QueryInterface* a_f4se, F4SE::PluginInfo* a_info)
{
    if (const auto data = F4SE::PluginVersionData::GetSingleton()) {
        a_info->infoVersion = F4SE::PluginInfo::kVersion;
        a_info->name = data->GetPluginName().data();
        a_info->version = data->GetPluginVersion().pack();
    }
    const auto ver = a_f4se->RuntimeVersion();
    if (ver < REL::Version(F4SE::RUNTIME_1_10_163)) {
        REX::ERROR("ExamineLagFix: unsupported runtime version {}", ver);
        return false;
    }
    return true;
}

F4SE_PLUGIN_LOAD(const F4SE::LoadInterface* a_f4se)
{
    F4SE::InitInfo initInfo{};
    initInfo.trampoline = true;
    initInfo.trampolineSize = 4096;
    F4SE::Init(a_f4se, initInfo);
    REX::INFO("ExamineLagFix: loaded");

    auto* messaging = F4SE::GetMessagingInterface();
    if (messaging) {
        messaging->RegisterListener([](F4SE::MessagingInterface::Message* a_msg) {
            if (a_msg->type == F4SE::MessagingInterface::kGameDataReady) {
                // Fix A must come first: its lazy-fill hook backstops the
                // scan suppression. Each fix fails independently.
                if (!InstallFixA()) {
                    REX::ERROR("ExamineLagFix: Fix A inactive (vanilla scan behavior)");
                }
                if (!InstallFixB()) {
                    REX::ERROR("ExamineLagFix: Fix B inactive (vanilla mod list behavior)");
                }
                if (!InstallFixC()) {
                    REX::ERROR("ExamineLagFix: Fix C inactive (vanilla entry list behavior)");
                }
            }
        });
    }
    return true;
}
