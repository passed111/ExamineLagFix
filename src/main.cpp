#include "F4SE/F4SE.h"
#include "RE/Fallout.h"
#include <REX/REX.h>
#include <Windows.h>
#include <atomic>
#include <chrono>
#include <cstring>
#include <cstdio>
#include <intrin.h>
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
    // Original UpdateItemList address as a plain integer (see InstallFixC).
    std::uintptr_t g_updateItemListAddr{ 0 };
    REL::Relocation<PopulateItemObj_t> g_origPopulate;

    // The engine caches the scrappable keyword in a .data global that the
    // vanilla scan reads directly. IDs: OG 515680, NG 2692427, AE 4799719.
    REL::Relocation<RE::BGSKeyword*> g_scrappableKwGlobal{ REL::VariantID(515680, 2692427, 4799719) };
    RE::BGSKeyword* g_scrappableKw = nullptr;

    // Fix C selective-populate state: active only while an inspect-mode
    // UpdateItemList is running. Plain stores/loads are fine - the list
    // build is single-threaded on the UI thread - but atomics keep the
    // populate hook's read honest under TSAN-style tooling.
    // ---- Pip-Boy inspect toggle -------------------------------------------
    // The filter builds one entry instead of the whole inventory. That is what
    // removes the stall, and it is what the pickup-examine flow is built around.
    //
    // The Pip-Boy inspect is the same menu in a different mode, and there the
    // cost is different: the panel supports paging through items with W/S, and
    // paging is a purely SWF-side action (moveSelectionDown) that reads the next
    // entryList entry, so it can only land on an entry that was built.
    //
    // What survives the filter is decided by the entry's handle id, which is a
    // single uint32 (InventoryInterface::Handle, +0x00 of the entry). Variants
    // of the same item share it: different mods of one weapon are separate
    // entries with the same handle, so all of them pass and W/S steps through
    // them. Unrelated items have a different handle and are not built, so a page
    // cannot reach them - that is the one real trade-off of the filter.
    //
    // The toml switch exists for anyone who wants every item paged-able anyway;
    // it costs the stall back.
    int g_fixInPipBoy = 1;

    // Minimal toml read: only "key = true|false" lines are understood, anything
    // else (comments, other keys, sections) is skipped. Missing file or key just
    // keeps the default, so a user never breaks the plugin with a typo.
    [[nodiscard]] std::wstring PluginDir()
    {
        HMODULE mod = nullptr;
        if (!GetModuleHandleExW(
                GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,
                reinterpret_cast<LPCWSTR>(&PluginDir), &mod) || !mod) {
            return {};
        }
        wchar_t path[MAX_PATH]{};
        if (!GetModuleFileNameW(mod, path, MAX_PATH)) return {};
        std::wstring s(path);
        const auto slash = s.find_last_of(L"\\/");
        if (slash == std::wstring::npos) return {};
        return s.substr(0, slash + 1);
    }

    [[nodiscard]] bool ReadTomlBool(const char* a_key, bool a_default)
    {
        const auto dir = PluginDir();
        if (dir.empty()) return a_default;
        const auto file = dir + L"ExamineLagFix.toml";

        FILE* f = nullptr;
        if (_wfopen_s(&f, file.c_str(), L"r") != 0 || !f) return a_default;

        bool result = a_default;
        char line[512]{};
        while (std::fgets(line, sizeof(line), f)) {
            std::string s(line);
            const auto hash = s.find('#');
            if (hash != std::string::npos) s = s.substr(0, hash);
            const auto eq = s.find('=');
            if (eq == std::string::npos) continue;

            auto key = s.substr(0, eq);
            auto val = s.substr(eq + 1);
            const auto trim = [](std::string& t) {
                const auto b = t.find_first_not_of(" \t\r\n");
                if (b == std::string::npos) { t.clear(); return; }
                const auto e = t.find_last_not_of(" \t\r\n");
                t = t.substr(b, e - b + 1);
            };
            trim(key);
            trim(val);
            if (key != a_key) continue;

            for (auto& c : val) c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
            result = (val == "true" || val == "1" || val == "yes" || val == "on");
            break;
        }
        std::fclose(f);
        return result;
    }

    std::atomic<bool>        g_selectivePop{ false };
    std::uint32_t            g_popTargetId{ 0 };   // ExamineMenu::modItem.id
    // Which stack of that item is being examined. The handle id alone cannot
    // tell three differently-modded 10mm pistols apart, so the entry filter
    // matches on id AND stack.
    std::uint32_t            g_popTargetStack{ 0 };// ExamineMenu::modStack
    std::atomic<std::uint32_t> g_popKept{ 0 };     // entries fully populated
    std::atomic<std::uint32_t> g_popSkipped{ 0 };  // entries skipped at populate

    // ---- runtime location of the per-entry callback ------------------- //
    // Both hard-coded prologues in InstallPerEntryHook match nothing on the
    // shipped 1.10.984 exe - its .text is packed, so no static byte pattern
    // exists to match - and the hook silently stayed uninstalled. That is the
    // whole reason inspecting never dropped below ~210ms: layer 2 skipped the
    // populate, but the walk still pushed all ~2880 entries.
    //
    // So the helper is captured live instead. Populate is called from inside it,
    // so the return address recorded on the first populate of a rebuild sits in
    // the helper's own body; walking back from there yields its entry point.
    // The first rebuild after load pays the vanilla cost once, every one after
    // that is filtered.
    std::atomic<std::uintptr_t> g_perEntryProbe{ 0 };  // return addr inside helper
    std::atomic<bool>           g_perEntryResolved{ false };
    std::atomic<bool>           g_perEntryBroken{ false };  // wrong function - stay vanilla
    std::atomic<bool>          g_inUpdateItemList{ false };

    // Census of who calls populate during one rebuild. The per-entry helper
    // invokes it once per native entry, so it wins the count by a mile - which
    // identifies it without matching a single byte. Walking the call graph
    // instead failed: UpdateItemList is only 0xBE9 bytes and none of its direct
    // call targets is anywhere near the address that actually calls populate,
    // so the helper is reached through at least one more hop.
    constexpr std::size_t kCallerSlots = 8;
    std::atomic<std::uintptr_t> g_callerRet[kCallerSlots];
    std::atomic<std::uint32_t>  g_callerN[kCallerSlots];
    std::atomic<std::uint32_t>  g_perEntryTries{ 0 };
    // Set whenever the GetSelectedIndex override runs, i.e. the patch really is
    // on the display path. Layer 1 is only allowed to shrink the list while this
    // is proven - see the self-check in HookedUpdateItemList.
    std::atomic<bool>           g_selIdxSeen{ false };
    std::atomic<std::uint32_t>  g_selectiveTries{ 0 };

    // Timing breakdown of one rebuild, so the log can say whether the cost is
    // in the walk itself or somewhere around it.
    std::atomic<std::int64_t>  g_tFirstPop{ 0 };
    std::atomic<std::int64_t> g_tLastPop{ 0 };
    std::atomic<std::uint32_t> g_popSeen{ 0 };
    std::atomic<std::int64_t> g_tBeforeOrig{ 0 };
    std::atomic<std::int64_t> g_tAfterOrig{ 0 };
    std::atomic<bool>         g_targetIndexLocked{ false };

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

    // --- runtime location of the per-entry callback --------------------- //
    // InstallPerEntryHook pins that helper with two hard-coded prologues, and
    // neither matches the shipped 1.10.984 exe (packed .text - there is no
    // static byte pattern to find). It therefore never installed, and every
    // rebuild walked all ~2880 entries, pushing a GFx object per entry. That
    // is the residual ~210ms.
    //
    // These helpers find it at runtime instead: populate is invoked from
    // inside the per-entry helper, so the return address captured on the first
    // populate of a rebuild lies in that helper's body, and stepping back
    // over the preceding ret / 0xCC padding reaches its entry point.
    // ----------------------------------------------------------------------- //

    // Minimal x64 instruction-length decoder. Covers only what MSVC emits in
    // the prologues we displace - push/pop r64, mov/lea/add/sub/and with a
    // modrm (including SIB and rip-relative), ret, int3, nop - plus the REX
    // and operand-size prefixes. Anything else returns 0 so the caller gives
    // up rather than patch across an instruction boundary.
    [[nodiscard]] std::size_t InsnLen(const std::uint8_t* a_p, std::size_t a_avail)
    {
        std::size_t i = 0;
        bool rex = false;
        while (i < a_avail) {
            const auto b = a_p[i];
            if (b == 0x66 || b == 0x67 || b == 0xF2 || b == 0xF3 ||
                b == 0x2E || b == 0x36 || b == 0x3E || b == 0x26 ||
                b == 0x64 || b == 0x65) {
                ++i;
                continue;
            }
            if ((b & 0xF0) == 0x40) {
                rex = true;
                ++i;
                continue;
            }
            break;
        }
        if (i >= a_avail) return 0;

        const auto op = a_p[i++];
        bool modrm = false;
        std::size_t imm = 0;
        switch (op) {
        case 0x50: case 0x51: case 0x52: case 0x53:
        case 0x54: case 0x55: case 0x56: case 0x57:
        case 0x58: case 0x59: case 0x5A: case 0x5B:
        case 0x5C: case 0x5D: case 0x5E: case 0x5F:
            break;                       // push / pop r64 - no modrm
        case 0xC3: case 0xC2: case 0xCC: case 0x90:
            break;                        // ret / int3 / nop
        case 0x00: case 0x01: case 0x02: case 0x03:
        case 0x08: case 0x09: case 0x0A: case 0x0B:
        case 0x10: case 0x11: case 0x12: case 0x13:
        case 0x18: case 0x19: case 0x1A: case 0x1B:
        case 0x20: case 0x21: case 0x22: case 0x23:
        case 0x28: case 0x29: case 0x2A: case 0x2B:
        case 0x30: case 0x31: case 0x32: case 0x33:
        case 0x38: case 0x39: case 0x3A: case 0x3B:
        case 0x63: case 0x69: case 0x6B: case 0x80:
        case 0x81: case 0x83: case 0x84: case 0x85:
        case 0x86: case 0x87: case 0x88: case 0x89:
        case 0x8A: case 0x8B: case 0x8C: case 0x8D:
        case 0x8E: case 0x8F: case 0xC0: case 0xC1:
        case 0xD0: case 0xD1: case 0xD2: case 0xD3:
        case 0xF6: case 0xF7: case 0xFE: case 0xFF:
            modrm = true;
            break;
        default:
            return 0;                      // unknown encoding - never guess
        }

        if (op == 0x81) imm = 4;
        else if (op == 0x83) imm = 1;
        else if (op == 0x69 || op == 0x6B) imm = 4;
        else if (op == 0xC0 || op == 0xC1 || op == 0xD0 ||
                 op == 0xD1 || op == 0xD2 || op == 0xD3) {
            // shift group - no immediate
        } else if (op == 0xF6 || op == 0xF7) {
            imm = 1;                       // group3 with imm8 (test)
        }

        if (modrm) {
            if (i >= a_avail) return 0;
            const auto m = a_p[i++];
            const auto mod = m >> 6;
            const auto rm = m & 7;
            std::size_t disp = 0;
            if (mod == 1) disp = 1;
            else if (mod == 2) disp = 4;
            if (rm == 4) {                            // SIB
                if (i >= a_avail) return 0;
                const auto sib = a_p[i++];
                if (mod == 0 && (sib & 7) == 5) disp = 4;
            } else if (mod == 0 && rm == 5) {
                disp = 4;                         // rip-relative
            }
            i += disp;
        }
        i += imm;
        return (i <= a_avail) ? i : 0;
    }

    // How many whole instructions to overwrite so PatchFuncEntry's 14-byte
    // absolute jump fits. Decodes forward; bails on anything it cannot size.
    [[nodiscard]] std::size_t SafeHookSizeAt(std::uintptr_t a_addr)
    {
        constexpr std::size_t kNeed = 14;
        constexpr std::size_t kMax = 64;
        const auto* p = reinterpret_cast<const std::uint8_t*>(a_addr);
        std::size_t total = 0;
        while (total < kNeed) {
            if (kMax - total < 16) return 0;
            const auto n = InsnLen(p + total, kMax - total);
            if (n == 0) return 0;
            total += n;
        }
        return total;
    }

    int HookedPerEntry(void* a_ctx, void* a_entry);
    void ResolvePerEntryFromProbe();
    [[nodiscard]] std::uintptr_t CallTargetAt(std::uintptr_t a_fn, std::size_t a_off);
    [[nodiscard]] bool PlausibleCounter(const std::int32_t* a_p);

    // Tally one populate caller. Slots are claimed by CAS and never released,
    // so the census covers the whole rebuild with no lock.
    void NotePopulateCaller(std::uintptr_t a_ret)
    {
        for (std::size_t i = 0; i < kCallerSlots; ++i) {
            const auto cur = g_callerRet[i].load(std::memory_order_acquire);
            if (cur == a_ret) {
                g_callerN[i].fetch_add(1, std::memory_order_relaxed);
                return;
            }
            if (cur == 0) {
                std::uintptr_t expect = 0;
                if (g_callerRet[i].compare_exchange_strong(expect, a_ret,
                        std::memory_order_acq_rel)) {
                    g_callerN[i].fetch_add(1, std::memory_order_relaxed);
                    return;
                }
            }
        }
    }

    void ResetPopulateCensus()
    {
        for (std::size_t i = 0; i < kCallerSlots; ++i) {
            g_callerRet[i].store(0, std::memory_order_release);
            g_callerN[i].store(0, std::memory_order_release);
        }
    }

    void HookedPopulateInventoryItemObj(RE::ExamineMenu* a_menu, void* a_owner,
        const void* a_entry, void* a_itemObj);

    void HookedUpdateItemList(RE::ExamineMenu* a_menu, std::uint64_t a_idx)
    {
        const auto t0 = NowUs();
        ResetPopulateCensus();
        // inspectingSingleItem is the pickup-examine panel (no paging there).
        // The Pip-Boy inspect is inspectMode without it, and that one is
        // governed by the toml switch.
        const bool pipBoyInspect =
            a_menu != nullptr && a_menu->inspectMode && !a_menu->inspectingSingleItem;
        const bool selective =
            a_menu != nullptr && a_menu->inspectMode &&
            (!pipBoyInspect || g_fixInPipBoy != 0);
        // 防御二（运行时自检）—— 当前停用，整段注释保留备查。
        // 作用：HookedGetSelIdx 被调用即置 g_selIdxSeen；若第一层已装但连续
        // 几次 rebuild 都没被调用，说明覆盖不在显示路径上 → 自动禁用第一层
        // （第二层不改变列表长度，显示仍正确）。
        // 停用理由：13 字节签名已在 OG/NG/AE 四版实测唯一命中，此自检属冗余。
        // 若要恢复：反注释本段，并反注释 HookedGetSelIdx 里
        // g_selIdxSeen.store(true, ...) 那一行。
        //
        // if (g_origPerEntry != nullptr &&
        //     !g_perEntryBroken.load(std::memory_order_acquire)) {
        //     if (g_selIdxSeen.load(std::memory_order_acquire)) {
        //         g_selectiveTries.store(0, std::memory_order_release);
        //     } else if (g_selectiveTries.fetch_add(1, std::memory_order_relaxed) >= 2) {
        //         g_perEntryBroken.store(true, std::memory_order_release);
        //         REX::ERROR("ExamineLagFix: GetSelectedIndex override was never "
        //                    "consulted across several filtered rebuilds - layer 1 "
        //                    "disabled so the panel does not show a clamped entry");
        //     }
        // }

        if (selective) {
            g_popTargetId = a_menu->modItem.id;
            g_popTargetStack = a_menu->modStack;
            g_popKept.store(0);
            g_popSkipped.store(0);
            g_entrySkip.store(0);
            g_popSeen.store(0);
            g_tFirstPop.store(0);
            g_tLastPop.store(0);
            g_targetIndexLocked.store(false, std::memory_order_release);
            g_selectivePop.store(true, std::memory_order_release);
        }
        g_inUpdateItemList.store(true, std::memory_order_release);
        g_tBeforeOrig.store(NowUs(), std::memory_order_release);
        g_origUpdateItemList(a_menu, a_idx);
        g_tAfterOrig.store(NowUs(), std::memory_order_release);
        g_inUpdateItemList.store(false, std::memory_order_release);
        g_selectivePop.store(false, std::memory_order_release);
        // Only the slow ones are logged - this runs on every list refresh, so an
        // unconditional line would flood the log. A filtered rebuild with layer 1
        // live costs ~30ms on a large inventory (that is the walk over ~2880
        // native entries, which the filter cannot remove), so the bar is set at
        // 50ms: anything above it is a real regression, not normal operation.
        {
            const auto dt = NowUs() - t0;
            if (dt >= 50000) {
                // Breakdown: work before the walk, the walk as timed between
                // its first and last populate call, and work after it.
                const auto first = g_tFirstPop.load();
                const auto last = g_tLastPop.load();
                const auto pre = (first != 0) ? first - g_tBeforeOrig.load() : 0;
                const auto walk = (first != 0) ? last - first : 0;
                const auto post = (last != 0) ? g_tAfterOrig.load() - last : 0;
                REX::INFO("ExamineLagFix DIAG: slow UpdateItemList inspect={} took {}us "
                          "(preWalk={} walk={} postWalk={}) kept={} skipped={} "
                          "entrySkip={} seen={} layer1={} thread {}",
                    selective, static_cast<long long>(dt),
                    static_cast<long long>(pre), static_cast<long long>(walk),
                    static_cast<long long>(post), g_popKept.load(),
                    g_popSkipped.load(), g_entrySkip.load(), g_popSeen.load(),
                    g_origPerEntry != nullptr ? 1 : 0,
                    static_cast<std::uint32_t>(GetCurrentThreadId()));
            }
        }
        if (selective) {
            const auto kept = g_popKept.load();
            const auto targetIdx = g_targetIndex.exchange(-1);
            if (kept == 0) {
                // Nothing matched modItem - the item left the inventory
                // mid-open, or the id / stack read is wrong for this build.
                // Rebuild unfiltered so the panel still shows something real.
                REX::ERROR("ExamineLagFix: inspect rebuild matched nothing "
                           "(item 0x{:08X} stack {}, {} entries) - using the "
                           "full list instead",
                    g_popTargetId, g_popTargetStack,
                    g_popSkipped.load() + g_entrySkip.load());
                g_inUpdateItemList.store(true, std::memory_order_release);
                g_origUpdateItemList(a_menu, a_idx);
                g_inUpdateItemList.store(false, std::memory_order_release);
                return;
            }
            if (targetIdx < 0) {
                // Entries were skipped, yet the id AND stack match never landed
                // - so the examined entry could not be pinned down. Leaving it
                // there would let the override keep answering with a stale index
                // and the panel would show the wrong item, which is exactly the
                // class of bug this filter must never introduce. Rebuild
                // unfiltered instead: correct, slower.
                REX::ERROR("ExamineLagFix: inspect rebuild could not pin the "
                           "examined stack (item 0x{:08X} stack {}, kept={}) - "
                           "using the full list instead",
                    g_popTargetId, g_popTargetStack, kept);
                g_inUpdateItemList.store(true, std::memory_order_release);
                g_origUpdateItemList(a_menu, a_idx);
                g_inUpdateItemList.store(false, std::memory_order_release);
                return;
            }
            // Publish the examined entry's absolute index so the
            // GetSelectedIndex hook can answer CreateModdedInventoryItem
            // with it. The invoke re-asserts it on the SWF side as well -
            // RefreshList may have clamped it - but the hook is what
            // actually feeds the display.
            g_targetIndex.store(targetIdx, std::memory_order_release);
            g_targetMenu = a_menu;
            Scaleform::GFx::Value args[1]{ Scaleform::GFx::Value{ targetIdx } };
            a_menu->itemList.Invoke("selectedIndex", nullptr, args, 1);
        } else {
            // A non-inspect rebuild invalidates any recorded target index.
            g_targetIndex.store(-1, std::memory_order_release);
        }
        // Locate the per-entry helper from the rebuild we just ran, so the
        // next one is filtered. See ResolvePerEntryFromProbe.
        ResolvePerEntryFromProbe();
    }

    std::int64_t HookedGetSelIdx(RE::ExamineMenu* a_menu)
    {
        // Proof that this override really sits on the display path. Merely
        // succeeding at patching something is not enough: a build with different
        // bytes can put the patch on another function, and then the display keeps
        // using the clamped index while layer 1 still shrinks the list - which
        // 防御二（运行时自检）—— 当前停用，整行注释保留备查。
        // 恢复时反注释本行 + HookedUpdateItemList 里那段自检。
        // g_selIdxSeen.store(true, std::memory_order_release);

        const auto own = g_targetIndex.load(std::memory_order_acquire);
        if (own >= 0 && a_menu == g_targetMenu) {
            return own;
        }
        return g_origGetSelIdx(a_menu);
    }

    // Does this entry stand for the stack being examined?
    //
    // InventoryUserUIInterfaceEntry is
    //   +0x00 InventoryInterface::Handle  (a single uint32 id)
    //   +0x08 BSTSmallArray<uint8_t,4> stackIndex
    // and BSTSmallArray is BSTArray, whose layout is { data, size }. Several
    // stacks of one item share the id, so the id alone matches all of them -
    // which is why the filter also has to find the stack here.
    [[nodiscard]] bool EntryHasStack(const void* a_entry, std::uint32_t a_stack)
    {
        // Go through CommonLib's own type instead of hand-decoding offsets.
        // Reading "+0x08 is the data pointer" was wrong: BSTSmallArray carries
        // its allocator (heap pointer, inline buffer, capacity) ahead of the
        // array's _data, so +0x08 is the allocator's heap field - and when the
        // array is using its inline buffer that field is garbage. Indexing it
        // crashed the game (crash-2026-10-03-15-35-44.log).
        const auto* e = static_cast<const RE::InventoryUserUIInterfaceEntry*>(a_entry);
        if (!e) return false;
        const auto& stacks = e->stackIndex;
        const auto n = stacks.size();
        if (n == 0 || n > 64) return false;
        bool found = false;
        // SEH: the entry arrives from the engine's walk, and a wrong layout or
        // a torn entry must never take the game down - it only costs accuracy.
        __try {
            for (std::uint32_t i = 0; i < n; ++i) {
                if (stacks[i] == a_stack) { found = true; break; }
            }
        } __except (EXCEPTION_EXECUTE_HANDLER) {
            found = false;
        }
        return found;
    }

    int HookedPerEntry(void* a_ctx, void* a_entry)
    {
        // g_perEntryBroken means the address we resolved at runtime was not the
        // helper after all; from then on this layer just forwards and the
        // populate filter is left to do what it can.
        if (g_perEntryBroken.load(std::memory_order_acquire)) {
            return g_origPerEntry(a_ctx, a_entry);
        }
        if (!g_selectivePop.load(std::memory_order_acquire)) {
            return g_origPerEntry(a_ctx, a_entry);
        }
        if (a_ctx == nullptr || a_entry == nullptr) {
            // A real walk context is never null. Reaching here means the
            // patched address is not the helper's entry.
            g_perEntryBroken.store(true, std::memory_order_release);
            REX::ERROR("ExamineLagFix: [PE] null argument - patched address is not "
                       "the per-entry helper, layer 1 disabled");
            return g_origPerEntry(a_ctx, a_entry);
        }

        // Everything below reads engine structures through a layout this plugin
        // assumes rather than proves: ctx+0x10 holds the entry counter, and
        // a_entry is an InventoryUserUIInterfaceEntry whose first field is the
        // handle id. If the resolved helper is wrong, or the layout differs on
        // this build, those reads fault - so each one is guarded and a fault
        // only turns the layer off. It must never take the game down.
        {
            bool skip = false;
            bool stackHit = false;
            __try {
                const auto entryId = *static_cast<const std::uint32_t*>(a_entry);
                if (entryId != g_popTargetId) {
                    skip = true;
                } else {
                    stackHit = EntryHasStack(a_entry, g_popTargetStack);
                }
            } __except (EXCEPTION_EXECUTE_HANDLER) {
                g_perEntryBroken.store(true, std::memory_order_release);
                REX::ERROR("ExamineLagFix: per-entry probe faulted reading the "
                           "entry - layer 1 disabled");
                return g_origPerEntry(a_ctx, a_entry);
            }

            if (skip) {
                __try {
                    auto* counter = *reinterpret_cast<std::int32_t**>(
                        static_cast<std::byte*>(a_ctx) + 0x10);
                    if (!PlausibleCounter(counter)) {
                        g_perEntryBroken.store(true, std::memory_order_release);
                        REX::ERROR("ExamineLagFix: [PE] ctx+0x10 does not hold an "
                                   "entry counter - refusing the write, layer 1 "
                                   "disabled");
                        return g_origPerEntry(a_ctx, a_entry);
                    }
                    ++*counter;
                } __except (EXCEPTION_EXECUTE_HANDLER) {
                    g_perEntryBroken.store(true, std::memory_order_release);
                    return g_origPerEntry(a_ctx, a_entry);
                }
                g_entrySkip.fetch_add(1);
                return 1;  // vanilla always returns 1; 0 would abort the walk
            }

            if (stackHit) {
                __try {
                    auto* counter = *reinterpret_cast<std::int32_t**>(
                        static_cast<std::byte*>(a_ctx) + 0x10);
                    if (PlausibleCounter(counter)) {
                        bool expected = false;
                        if (g_targetIndexLocked.compare_exchange_strong(expected, true,
                                std::memory_order_acq_rel)) {
                            g_targetIndex.store(*counter, std::memory_order_release);
                        }
                    }
                } __except (EXCEPTION_EXECUTE_HANDLER) {
                    g_perEntryBroken.store(true, std::memory_order_release);
                }
            }
            return g_origPerEntry(a_ctx, a_entry);
        }
    }


    // The walk counter is an index into the native entry array, so whatever it
    // points at must currently hold a small non-negative number. Used to refuse
    // a write through anything else: a wrong context layout would scribble over
    // engine memory and only surface later, as a jump into garbage
    // (crash-2026-10-03-23-19-32.log executed 0x007D80000000).
    [[nodiscard]] bool PlausibleCounter(const std::int32_t* a_p)
    {
        if (!a_p) return false;
        if (reinterpret_cast<std::uintptr_t>(a_p) < 0x10000) return false;
        const auto v = *a_p;
        return v >= 0 && v < 200000;
    }

    // Sanity check on an address FunctionEntryFrom() backtracked to: the first
    // byte must be a plausible MSVC x64 function start (a REX-prefixed push, a
    // bare push rbp/rbx/rsi/rdi, or the mov/sub/lea/xor that opens a frame).
    // Data, or the middle of an instruction, will not match - and we would rather
    // skip layer 1 than patch something random.
    [[nodiscard]] bool LooksLikePrologue(std::uintptr_t a_addr)
    {
        if (!IsInsideExe(a_addr)) return false;
        std::uint8_t b0 = 0;
        __try {
            b0 = *reinterpret_cast<const std::uint8_t*>(a_addr);
        } __except (EXCEPTION_EXECUTE_HANDLER) {
            return false;
        }
        if ((b0 & 0xF0) == 0x40) return true;    // REX: push r8-r15 etc.
        switch (b0) {
        case 0x55: case 0x53: case 0x56: case 0x57:   // push rbp/rbx/rsi/rdi
        case 0x48: case 0x4C: case 0x4D: case 0x44:   // mov/sub/lea with REX.W
        case 0x45: case 0x33: case 0x8B: case 0x89: case 0x8D:
            return true;
        default:
            return false;
        }
    }

    // Install layer 1 on an address that was resolved at runtime, not from a
    // hard-coded byte pattern (see ResolvePerEntryFromProbe for why).
    bool InstallPerEntryHookAt(std::uintptr_t a_addr)
    {
        if (g_origPerEntry) return true;
        if (!IsInsideExe(a_addr)) return false;
        const auto size = SafeHookSizeAt(a_addr);
        if (size == 0) return false;
        const auto stub = PatchFuncEntry(a_addr, size, &HookedPerEntry, "PerEntry");
        if (!stub) return false;
        g_origPerEntry = reinterpret_cast<PerEntryFn>(stub);
        return true;
    }

    // Windows x64 exception directory. A sorted array of
    //   struct RUNTIME_FUNCTION { DWORD Begin; DWORD End; DWORD UnwindData; };
    // covering every function in the image. The OS uses it to unwind, so it is
    // always present and always exact - unlike scanning for a 0xC3 (that byte
    // shows up inside immediates just as often) or matching prologue bytes
    // (which are not there at all in a packed image).
    struct RuntimeFunction { std::uint32_t begin; std::uint32_t end; std::uint32_t unwind; };

    // Exact [begin, size) of the function containing a_addr, from .pdata.
    [[nodiscard]] bool PdataBounds(std::uintptr_t a_addr, std::uintptr_t* a_beginOut,
        std::size_t* a_sizeOut)
    {
        const auto base = reinterpret_cast<std::uintptr_t>(GetModuleHandleW(nullptr));
        if (!base || a_addr < base) return false;
        auto* dos = reinterpret_cast<IMAGE_DOS_HEADER*>(base);
        if (dos->e_magic != IMAGE_DOS_SIGNATURE) return false;
        auto* nt = reinterpret_cast<IMAGE_NT_HEADERS*>(base + dos->e_lfanew);
        if (nt->Signature != IMAGE_NT_SIGNATURE) return false;
        const auto rva = static_cast<std::uint32_t>(a_addr - base);

        auto* sec = IMAGE_FIRST_SECTION(nt);
        for (std::uint32_t i = 0; i < nt->FileHeader.NumberOfSections; ++i, ++sec) {
            if (std::memcmp(sec->Name, ".pdata", 6) != 0) continue;
            const auto* tbl = reinterpret_cast<const std::uint8_t*>(base + sec->VirtualAddress);
            const auto n = sec->Misc.VirtualSize / sizeof(RuntimeFunction);
            std::size_t lo = 0;
            std::size_t hi = n;
            while (lo < hi) {
                const auto mid = lo + (hi - lo) / 2;
                const auto* e = reinterpret_cast<const RuntimeFunction*>(tbl) + mid;
                if (rva < e->begin) { hi = mid; }
                else if (rva >= e->end) { lo = mid + 1; }
                else {
                    // MSVC splits a function into consecutive chunks, each with
                    // its own RUNTIME_FUNCTION entry. The entry of the FIRST
                    // chunk is the only address that is safe to patch - a later
                    // chunk starts mid-function, and hooking there makes the
                    // engine fall into the hook with live registers destroyed
                    // (crash-2026-10-03-23-19-32.log). So walk back over
                    // contiguous entries and report the outermost begin.
                    std::size_t first = mid;
                    std::size_t guard = 0;
                    while (first > 0 && guard < 8) {
                        const auto* prev =
                            reinterpret_cast<const RuntimeFunction*>(tbl) + (first - 1);
                        const auto* cur =
                            reinterpret_cast<const RuntimeFunction*>(tbl) + first;
                        if (prev->end != cur->begin) break;
                        --first;
                        ++guard;
                    }
                    const auto* head =
                        reinterpret_cast<const RuntimeFunction*>(tbl) + first;
                    *a_beginOut = base + head->begin;
                    *a_sizeOut = static_cast<std::size_t>(
                        reinterpret_cast<const RuntimeFunction*>(tbl)[mid].end - head->begin);
                    return true;
                }
            }
            return false;
        }
        return false;
    }

    // Walk back from an address inside a function to that function's entry.
    //
    // Scanning for a bare 0xC3 is not reliable: that byte appears inside
    // immediates and modrm bytes just as often as at a real return. So each
    // position that looks like a function start is treated as a candidate and
    // decoded forward - it only counts when the walk lands exactly on a_inside.
    // Scanning outward from the closest position first means the first clean
    // candidate is the right one.
    [[nodiscard]] std::uintptr_t FunctionEntryFrom(std::uintptr_t a_inside)
    {
        if (!IsInsideExe(a_inside)) return 0;
        constexpr std::size_t kMaxBack = 0x1000;
        for (std::size_t back = 1; back <= kMaxBack; ++back) {
            const auto cand = a_inside - back;
            if (!IsInsideExe(cand)) return 0;
            // MSVC x64 starts functions on a 16-byte boundary. Requiring it cuts
            // the false positives by 16x - without it, some random offset a few
            // bytes back always manages to decode cleanly onto the target.
            if ((cand & 15) != 0) continue;
            if (!LooksLikePrologue(cand)) continue;
            std::size_t off = 0;
            bool clean = true;
            while (off < back) {
                const auto n = InsnLen(
                    reinterpret_cast<const std::uint8_t*>(cand) + off, back - off);
                if (n == 0) { clean = false; break; }
                off += n;
            }
            if (clean && off == back) return cand;
        }
        return 0;
    }

    // Resolve and install layer 1 from the populate call we just observed.
    //
    // InstallPerEntryHook pins the helper with two hard-coded prologues, and
    // neither matches the shipped 1.10.984 exe, so layer 1 never installed and
    // every inspect rebuild kept walking all ~2880 native entries, pushing a
    // GFx object for each one - the residual ~210ms.
    //
    // Two facts shape the runtime lookup:
    //   * the vtable slot cannot be used as a scan base - another mod hooks
    //     ExamineMenu slot 0x2F first, so the slot holds their stub, which is not
    //     even inside the exe (scanning it found no in-exe calls at all);
    //   * populate is invoked from inside the per-entry helper, so the return
    //     address captured in the populate hook lies in that helper's body.
    //
    // So: capture the return address, walk back to the enclosing entry, and
    // confirm it against the calls UpdateItemList makes. Only then patch.
    void ResolvePerEntryFromProbe()
    {
        if (g_origPerEntry != nullptr) return;
        if (g_perEntryResolved.load(std::memory_order_acquire)) return;

        // HARD PRECONDITION: layer 1 may only run while the GetSelectedIndex
        // override is live.
        //
        // Skipping entries shrinks the SWF list, and RefreshList then clamps
        // its selectedIndex. The display path reads that clamped index back and
        // indexes the native entry array with it - so without the override
        // answering with the recorded absolute index, every examine shows
        // whatever sits at the clamped position: one fixed item for the whole
        // session (the 1.1.0 regression - users on OG saw .308 ammo / some note
        // for everything). GetSelectedIndex is only patched where its signature
        // is verified, and that does not include OG, so on OG we must stay on
        // the populate-only filter: slower, but the display stays correct.
        if (g_origGetSelIdx == nullptr) {
            g_perEntryResolved.store(true, std::memory_order_release);
            REX::INFO("ExamineLagFix: GetSelectedIndex override not available on "
                      "this runtime - layer 1 left off, populate filter only");
            return;
        }

        g_perEntryProbe.exchange(0, std::memory_order_acq_rel);

        // The helper is the caller that fires once per entry. Everything else
        // calls populate a handful of times at most, so the count alone picks
        // it out - no byte matching, no call-graph walk.
        const auto seen = g_popSeen.load(std::memory_order_relaxed);
        std::uintptr_t bestRet = 0;
        std::uint32_t bestN = 0;
        for (std::size_t i = 0; i < kCallerSlots; ++i) {
            const auto n = g_callerN[i].load(std::memory_order_relaxed);
            if (n > bestN) {
                bestN = n;
                bestRet = g_callerRet[i].load(std::memory_order_relaxed);
            }
        }

        // Only the first rebuild dumps the census - it is diagnostic, and this
        // runs per rebuild until the helper is found.
        if (g_perEntryTries.load(std::memory_order_relaxed) != 0) {
            // fall through to the decision below
        } else
        for (std::size_t i = 0; i < kCallerSlots; ++i) {
            const auto ret = g_callerRet[i].load(std::memory_order_relaxed);
            if (ret == 0) continue;
            std::uintptr_t fnBegin = 0;
            std::size_t fnSize = 0;
            if (PdataBounds(ret, &fnBegin, &fnSize)) {
                REX::INFO("ExamineLagFix: [CENSUS] caller 0x{:X} x{} -> fn 0x{:X} "
                          "(RVA 0x{:X}, size 0x{:X})",
                    ret, g_callerN[i].load(std::memory_order_relaxed), fnBegin,
                    static_cast<std::uint32_t>(fnBegin -
                        reinterpret_cast<std::uintptr_t>(GetModuleHandleW(nullptr))),
                    fnSize);
            }
        }

        // Require the winner to account for most of the calls: a helper that
        // runs per entry cannot be a minority caller. A rebuild that barely
        // calls populate is not evidence either way, so keep trying for a few
        // rounds before giving up.
        if (bestRet == 0 || seen == 0 || bestN * 2 < seen) {
            const auto tries = g_perEntryTries.fetch_add(1, std::memory_order_relaxed) + 1;
            if (tries <= 5) return;
            REX::ERROR("ExamineLagFix: per-entry helper not identified after {} "
                       "rebuilds - best caller 0x{:X} x{} out of {} populate "
                       "calls - layer 1 stays off", tries, bestRet, bestN, seen);
            g_perEntryResolved.store(true, std::memory_order_release);
            return;
        }

        std::uintptr_t fnBegin = 0;
        std::size_t fnSize = 0;
        bool haveBounds = false;
        __try {
            haveBounds = PdataBounds(bestRet, &fnBegin, &fnSize);
        } __except (EXCEPTION_EXECUTE_HANDLER) {
            haveBounds = false;
        }

        auto decoded = haveBounds ? fnBegin : FunctionEntryFrom(bestRet);
        // .pdata can hand back a chunk start rather than the function start -
        // on 1.10.984 it reported 0xA18F31 for a helper that actually begins at
        // 0xA18EF0, and patching 65 bytes into the body made the engine fall
        // into this hook from the middle of the function with unrelated
        // arguments (crash-2026-10-03-23-05-23.log). Function entries are
        // 16-byte aligned, so an unaligned answer is not one.
        if (decoded != 0 && (decoded & 15) != 0) {
            const auto aligned = FunctionEntryFrom(decoded);
            if (aligned != 0) {
                REX::INFO("ExamineLagFix: [PDATA] 0x{:X} is not 16-byte aligned, "
                          "using the aligned start 0x{:X} instead", decoded, aligned);
                fnSize += static_cast<std::size_t>(decoded - aligned);
                decoded = aligned;
            }
        }
        if (decoded == 0) {
            REX::ERROR("ExamineLagFix: per-entry helper entry not resolvable "
                       "from caller 0x{:X} - layer 1 stays off", bestRet);
            g_perEntryResolved.store(true, std::memory_order_release);
            return;
        }

        bool ok = false;
        __try {
            ok = InstallPerEntryHookAt(decoded);
        } __except (EXCEPTION_EXECUTE_HANDLER) {
            ok = false;
        }

        g_perEntryResolved.store(true, std::memory_order_release);
        if (ok) {
            char hex[128];
            int n = 0;
            __try {
                for (int i = 0; i < 32; ++i) {
                    n += std::snprintf(hex + n, sizeof(hex) - n, "%02X ",
                        *reinterpret_cast<const std::uint8_t*>(decoded + i));
                }
            } __except (EXCEPTION_EXECUTE_HANDLER) {
                n = 0;
            }
            REX::INFO("ExamineLagFix: per-entry helper located at runtime @ 0x{:X} "
                      "(RVA 0x{:X}, size 0x{:X}, called populate x{}, from 0x{:X}) [{}]",
                decoded, static_cast<std::uint32_t>(decoded -
                    reinterpret_cast<std::uintptr_t>(GetModuleHandleW(nullptr))),
                fnSize, bestN, bestRet, n > 0 ? hex : "<unreadable>");
        } else {
            g_perEntryBroken.store(true, std::memory_order_release);
            REX::ERROR("ExamineLagFix: per-entry helper @ 0x{:X} could not be "
                       "patched - layer 1 disabled", decoded);
        }
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

    // rel32 target of the E8 at a_fn+a_off, or 0 when that byte is not a call.
    // Used to reach helpers that have no address-library ID by walking the body
    // of the function that calls them.
    [[nodiscard]] std::uintptr_t CallTargetAt(std::uintptr_t a_fn, std::size_t a_off)
    {
        const auto* p = reinterpret_cast<const std::uint8_t*>(a_fn + a_off);
        if (p[0] != 0xE8) return 0;
        const auto tgt = a_fn + a_off + 5 + *reinterpret_cast<const std::int32_t*>(p + 1);
        return IsInsideExe(tgt) ? tgt : 0;
    }

    // ---- 防御一（语义验证）——当前停用，整段注释保留备查 ----
    // 见 InstallGetSelIdxHook 里调用处的说明。恢复时反注释整段。
    //
    // // Semantic cross-check for a GetSelectedIndex candidate: its body has to
    // // reference the literal "selectedIndex" (that is the SWF property it reads).
    // //
    // // The string alone does NOT identify the function - roughly 25 functions in
    // // every build reference it (TerminalMenu::GetSelectedIndex,
    // // GetCurrentSlotKeyword, the ModSlotList helpers ...). It is used only to
    // // confirm or reject what the signature matched, which is what protects
    // // against a build whose bytes differ (the GOG OG report: layer 1 filtering
    // // while the override never fired, so every examine showed the alphabetically
    // // first entry instead).
    // //
    // // Only the candidate's own body is scanned (~130 bytes), not all of .text.
    // [[nodiscard]] bool BodyReferencesSelIdxString(std::uintptr_t a_addr)
    // {
    //     static constexpr char kStr[]{ "selectedIndex" };
    //     constexpr std::size_t kLen = sizeof(kStr) - 1;
    //
    //     const auto base = reinterpret_cast<std::uintptr_t>(GetModuleHandleW(nullptr));
    //     if (!base || a_addr < base) return false;
    //     auto* dos = reinterpret_cast<IMAGE_DOS_HEADER*>(base);
    //     if (dos->e_magic != IMAGE_DOS_SIGNATURE) return false;
    //     auto* nt = reinterpret_cast<IMAGE_NT_HEADERS*>(base + dos->e_lfanew);
    //     if (nt->Signature != IMAGE_NT_SIGNATURE) return false;
    //
    //     std::uint32_t strRva[8];
    //     std::size_t nStr = 0;
    //     std::uintptr_t textVa = 0;
    //     std::size_t textSize = 0;
    //
    //     auto* sec = IMAGE_FIRST_SECTION(nt);
    //     bool ok = true;
    //     __try {
    //         for (std::uint32_t i = 0; i < nt->FileHeader.NumberOfSections && ok; ++i, ++sec) {
    //             const auto sz = sec->Misc.VirtualSize ? sec->Misc.VirtualSize : sec->SizeOfRawData;
    //             if (sz == 0) continue;
    //             const auto* b = reinterpret_cast<const std::uint8_t*>(base + sec->VirtualAddress);
    //             if (std::memcmp(sec->Name, ".text", 5) == 0) {
    //                 textVa = sec->VirtualAddress;
    //                 textSize = sz;
    //             }
    //             if ((sec->Characteristics & IMAGE_SCN_MEM_WRITE) != 0) continue;
    //             // memchr for the first byte, then compare - avoids a 13-byte
    //             // memcmp at every position of a multi-MB section.
    //             const auto* p = b;
    //             const auto* endB = b + (sz >= kLen ? sz - kLen : 0);
    //             while (p <= endB && nStr < 8) {
    //                 p = reinterpret_cast<const std::uint8_t*>(
    //                     std::memchr(p, kStr[0], static_cast<std::size_t>(endB - p) + 1));
    //                 if (!p) break;
    //                 if (std::memcmp(p, kStr, kLen) == 0) {
    //                     strRva[nStr++] = static_cast<std::uint32_t>(sec->VirtualAddress + (p - b));
    //                 }
    //                 ++p;
    //             }
    //         }
    //     } __except (EXCEPTION_EXECUTE_HANDLER) {
    //         return false;
    //     }
    //     if (nStr == 0 || textSize == 0) return false;
    //
    //     std::uintptr_t begin = 0;
    //     std::size_t size = 0;
    //     if (!PdataBounds(a_addr, &begin, &size) || size == 0 || size > 0x1000) return false;
    //
    //     bool found = false;
    //     __try {
    //         const auto* body = reinterpret_cast<const std::uint8_t*>(begin);
    //         for (std::size_t i = 0; i + 7 <= size && !found; ++i) {
    //             // REX.W/S/B/D  lea  reg,[rip+rel32]   (7 bytes)
    //             if (body[i] < 0x40 || body[i] > 0x4F) continue;
    //             if (body[i + 1] != 0x8D) continue;
    //             const auto modrm = body[i + 2];
    //             if ((modrm & 0xC7) != 0x05) continue;      // mod=00 rm=101
    //             const auto rel = *reinterpret_cast<const std::int32_t*>(body + i + 3);
    //             const auto tgt = static_cast<std::uint32_t>(
    //                 textVa + (begin - base) + i + 7 + rel);
    //             for (std::size_t s = 0; s < nStr; ++s) {
    //                 if (tgt == strRva[s]) { found = true; break; }
    //             }
    //         }
    //     } __except (EXCEPTION_EXECUTE_HANDLER) {
    //         return false;
    //     }
    //     return found;
    // }

    bool InstallGetSelIdxHook()
    {
        // ExamineMenu::GetSelectedIndex - reads the SWF "selectedIndex" off
        // ItemList and returns it as an int. Its body measures 127 bytes on 155
        // and OG, 129 on NG and AE.
        //
        // 13-byte prologue, byte-verified unique (exactly one hit) and landing
        // on the right function on ALL FOUR images checked offline:
        //   OG 1.10.163  -> RVA 0xB1B280 (size 127)
        //   NG 1.10.984  -> RVA 0xA0DAA0 (size 129)
        //   AE 1.11.221  -> RVA 0xA61670 (size 129)
        //   AE 1.11.240  -> RVA 0xA61980 (size 129)
        //
        //   40 53                    push rbx
        //   48 83 EC 50              sub rsp,0x50
        //   48 8B 91 98 04 00 00     mov rdx,[rcx+0x498]   <- ItemList
        //
        // The previous 18-byte signature appended `lea r9,[rsp+0x30]`. OG emits
        // `xor eax,eax` first and the lea afterwards, so that signature matched
        // nothing on OG - the hook silently stayed off there and layer 1 was
        // unavailable to OG users. Dropping the trailing lea keeps the part all
        // builds agree on.
        static constexpr std::uint8_t kPro[]{
            0x40, 0x53, 0x48, 0x83, 0xEC, 0x50,
            0x48, 0x8B, 0x91, 0x98, 0x04, 0x00, 0x00 };

        const auto addr = ScanTextSig(kPro, sizeof(kPro), nullptr, 0, true, "GetSelIdx");
        if (!addr) return false;

        // 防御一（语义验证）—— 当前停用，整段注释保留备查。
        // 作用：签名命中的函数，其函数体必须真的引用 "selectedIndex" 字面量
        // （用 .pdata 圈出函数范围，只扫那 ~130 字节找 rip-relative LEA 指向
        // 字符串 RVA）。防的是"字节不同的构建上 13 字节签名命中了别的函数"。
        // 停用理由：13 字节签名已在 OG/NG/AE 四版实测唯一命中，此校验属冗余。
        // 若要恢复：反注释本段，并反注释 BodyReferencesSelIdxString 的定义
        // （它在本文件 InstallGetSelIdxHook 之前）。
        //
        // if (!BodyReferencesSelIdxString(addr)) {
        //     REX::ERROR("ExamineLagFix: GetSelectedIndex signature hit 0x{:X} does not "
        //                "reference the \"selectedIndex\" property - wrong function, "
        //                "hook NOT installed", addr);
        //     return false;
        // }

        // The 13 matched bytes are shorter than the 14-byte absolute jump, so
        // the displacement is decoded forward instead of being assumed. The
        // bounds check from .pdata also rules out matching the same bytes in
        // the middle of some other function.
        std::uintptr_t fnBegin = 0;
        std::size_t fnSize = 0;
        if (PdataBounds(addr, &fnBegin, &fnSize) && fnBegin != addr) {
            REX::ERROR("ExamineLagFix: GetSelectedIndex signature hit 0x{:X} is not a "
                       "function entry (starts at 0x{:X}) - hook NOT installed",
                addr, fnBegin);
            return false;
        }
        if (fnSize != 0 && (fnSize < 100 || fnSize > 200)) {
            REX::ERROR("ExamineLagFix: GetSelectedIndex candidate 0x{:X} has size {}, "
                       "outside the 100-200 seen on every build - hook NOT installed",
                addr, fnSize);
            return false;
        }
        const auto hookSize = SafeHookSizeAt(addr);
        if (hookSize == 0) {
            REX::ERROR("ExamineLagFix: GetSelectedIndex prologue at 0x{:X} does not "
                       "decode cleanly - hook NOT installed", addr);
            return false;
        }

        const auto stub = PatchFuncEntry(addr, hookSize, &HookedGetSelIdx, "GetSelIdx");
        if (!stub) return false;
        g_origGetSelIdx = reinterpret_cast<GetSelIdxFn>(stub);
        REX::INFO("ExamineLagFix: GetSelectedIndex hooked @ 0x{:X} ({} bytes displaced, "
                  "function size {})", addr, hookSize, fnSize);
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
            // Not fatal on its own: the helper is also located at runtime from
            // the populate caller census (see ResolvePerEntryFromProbe), which is
            // what actually finds it on current builds. The signature route is
            // kept for the runtimes where it still matches.
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
        g_fixInPipBoy = ReadTomlBool("InspectFixInPipBoy", true) ? 1 : 0;
        REX::INFO("ExamineLagFix: Pip-Boy inspect filter {} (ExamineLagFix.toml, "
                  "InspectFixInPipBoy)",
            g_fixInPipBoy != 0 ? "ON" : "OFF (paging works, stall returns)");
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
        // write_vfunc returns the slot's original, which is the real function
        // address - keep it as a plain integer too. (g_origUpdateItemList is a
        // Relocation, and its .address() is NOT that address; using it for a
        // body scan scanned the wrong place and found no calls at all.)
        // Read the slot BEFORE patching it. The value logged as "originals"
        // below is read after the swap, so it is our hook, not the original -
        // and what write_vfunc returns is not the original either. Both were
        // used as a body-scan base and both produced no call targets at all.
        // Real UpdateItemList address, for the per-entry helper scan below.
        //
        // It deliberately does NOT come from the vtable slot. Another mod hooks
        // ExamineMenu slot 0x2F before us, so the slot holds their stub, which
        // is not even inside the exe - scanning that found no in-exe calls at
        // all. REL::Relocation::address() is not a function address either, it
        // is the variable's own storage. The address library ID is the only
        // reliable source.
        REL::Relocation<std::uintptr_t> ulRelUpdate{ REL::VariantID(762897, 2224143) };
        g_updateItemListAddr = ulRelUpdate.address();
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
        // The signature route is tried first because it makes layer 1 live from
        // the very first rebuild. Where it does not match, ResolvePerEntryFromProbe
        // finds the helper at runtime instead - see its comment for why.
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
        // Locating layer 1: populate is invoked from inside the per-entry
        // helper, so while a rebuild is in flight the return address of that
        // call lies in the helper's body. Tally every distinct caller, so the
        // one that fires once per entry can be picked out by count.
        if (g_inUpdateItemList.load(std::memory_order_acquire)) {
            const auto ret = reinterpret_cast<std::uintptr_t>(_ReturnAddress());
            NotePopulateCaller(ret);
            if (g_perEntryProbe.load(std::memory_order_relaxed) == 0) {
                g_perEntryProbe.store(ret, std::memory_order_release);
            }
        }

        // Walk timing: first to last populate call is the span the entry loop
        // actually spends visiting entries.
        const auto now = NowUs();
        g_popSeen.fetch_add(1, std::memory_order_relaxed);
        if (g_tFirstPop.load(std::memory_order_relaxed) == 0) {
            g_tFirstPop.store(now, std::memory_order_release);
        }
        g_tLastPop.store(now, std::memory_order_release);

        // Layer 2 (safety net). Matches on the handle id alone - several stacks
        // of one item share it, so every variant of the inspected weapon is built
        // and W/S can page between them. Which one the panel shows is decided by
        // the id AND stack capture in HookedPerEntry, not here.
        if (g_selectivePop.load(std::memory_order_acquire)) {
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
