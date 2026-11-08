import Mathlib

/-!
# SharedCorridorFootprint

`EcoLib.Corridors.SharedCorridorFootprint` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-canon` at commit `d43fad229ded`
- `series/SFMC/ViridisRun173.lean` (SHA-256 `b2aec63bfa1ab8b9…`)
Certification: COMPARATOR_CLOUD, evidence `series/SFMC/COMPARATOR_SUMMARY.md`
Engine run: Run-173
Public since: 2026-09-27

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

namespace Viridis.HDFM.SharedCorridorFootprint

theorem shared_saving
    (a b s : Nat) (hsa : s ≤ a) (hsb : s ≤ b) :
    a + b - (a + b - s) = s := by
  omega

theorem combined_le_gross
    (a b s : Nat) :
    a + b - s ≤ a + b := by
  omega

theorem combined_covers_left
    (a b s : Nat) (hsb : s ≤ b) :
    a ≤ a + b - s := by
  omega

theorem combined_covers_right
    (a b s : Nat) (hsa : s ≤ a) :
    b ≤ a + b - s := by
  omega

theorem left_footprint_contained
    (a b : Nat) (hab : a ≤ b) :
    a + b - a = b := by
  omega

theorem shared_corridor_witness :
    8 + 11 - 5 = 14 := by
  norm_num

end Viridis.HDFM.SharedCorridorFootprint
