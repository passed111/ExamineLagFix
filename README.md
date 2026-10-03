# ExamineLagFix

Removes the synchronous stall when the **ExamineMenu** opens — the pickup-examine
panel for legendary weapons / magazines / featured items, and the inspect panel
inside the Pip-Boy.

On a large inventory the menu took well over a second to appear. Three separate
pieces of synchronous work caused it, all of which run before the menu's first
visible frame. Each is fixed independently and each fails independently — if any
hook cannot be verified it stays uninstalled and that part behaves like vanilla.

## What it fixes

### A — scrappable-recipe scan

`SetUpExamineMenu` rebuilds `scrappableItemsMap` on **every** menu open by walking
the whole COBJ form array and running a keyword check per recipe. The map's only
consumer is `BuildWeaponScrappingArray`, which the examine flow never calls unless
the player actually scraps the item — so the scan is wasted work virtually always.

Fix: the COBJ array size is temporarily zeroed for the duration of the original
call (the scan loop then runs zero iterations), and `BuildWeaponScrappingArray` is
hooked to rebuild the map lazily, through the vanilla predicate, right before the
engine reads it. Scrapping still behaves identically.

### B — mod list build

For weapons and armor, `BuildPossibleModList` re-evaluates every COBJ recipe
(attach point match + condition tree + `CanBeUsedOn`) to build an installable-mod
list that inspect mode never displays. The "currently attached mods" preview comes
from `FindWeaponMods` via the instance data instead, and is left alone.

Fix: in inspect mode the choice array is torn down exactly as the vanilla
prologue does and the scan is skipped. Workbench mode runs vanilla.

### C — inventory entry-list rebuild

The examine SWF is a full workbench menu (mod select, item select, featured item)
that also has an inspect mode, and its AS3 init callback unconditionally rebuilds
the **entire** inventory entry list on every open — visiting every carried item
and pushing one Scaleform object per entry into an `entryList` the inspect UI
never displays.

Fix: the rebuild still runs (its result feeds the display), but the expensive
parts are filtered in two layers:

1. **per-entry callback** — entries other than the examined item return early,
   skipping the Scaleform invokes, the populate, and the `entryList` push.
2. **populate** — independently skips the per-entry display-data build, covering
   the case where layer 1 could not be installed.

Layer 1 is what actually removes the stall: measured on 1.10.984 with ~2880 native
entries, the rebuild went from **223 ms to 30 ms**, with the per-entry walk itself
dropping to zero.

## Configuration

`ExamineLagFix.toml`, next to the DLL:

```toml
InspectFixInPipBoy = true
```

- `true` (default) — the Pip-Boy inspect is filtered the same way the pickup
  panel is. Variants of the same item (several differently-modded copies of one
  weapon) are all built, so W/S still pages between them; unrelated items are not
  built, so a page cannot reach them. That is the one trade-off of the filter.
- `false` — the Pip-Boy inspect falls back to vanilla: the whole inventory is
  built, so paging to unrelated items works again, at the cost of the stall.

The pickup-examine panel is always filtered; it has no paging, so the switch does
not apply to it.

## Building

Requires [commonlibf4](https://github.com/Bobbyclue/commonlibf4) (or any fork with
the same xmake rules) side by side with this directory.

```
xmake build ExamineLagFix
```

## Notes on locating engine functions

Nothing is located by hardcoded RVA. Where an address-library ID exists it is used
directly. Where it does not — the per-entry callback being the case in point — the
function is found at runtime instead:

- the populate hook records who called it (`_ReturnAddress()`);
- the per-entry helper invokes populate once per native entry, so it wins the call
  count by a wide margin, which identifies it without matching any bytes;
- `.pdata` (the Windows x64 unwind table) then gives the exact function bounds
  via binary search. Its entries are **merged backwards over contiguous chunks**
  first — MSVC splits functions into chunks, and only the first chunk's begin is
  safe to patch.

Hardcoded prologue signatures are also tried first, because that makes layer 1
live from the very first rebuild, but they are a fast path, not the mechanism.
