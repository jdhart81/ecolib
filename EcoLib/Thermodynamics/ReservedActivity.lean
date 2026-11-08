import Mathlib

/-!
# ReservedActivity

`EcoLib.Thermodynamics.ReservedActivity` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-canon` at commit `d43fad229ded`
- `series/RASL/ViridisRun171.lean` (SHA-256 `2c49eaff46ed0340…`)
Certification: COMPARATOR_CLOUD, evidence `series/RASL/COMPARATOR_SUMMARY.md`
Engine run: Run-171
Public since: 2026-09-19

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

namespace Viridis.SpeedLimits.ReservedActivity

theorem reserved_activity_bound
    (progress ticks usable reserve : Nat)
    (hprogress : progress ≤ ticks * usable) :
    progress + ticks * reserve ≤ ticks * (usable + reserve) := by
  have h := Nat.add_le_add_right hprogress (ticks * reserve)
  simpa only [Nat.mul_add] using h

theorem zero_usable_forces_zero
    (progress ticks : Nat)
    (hprogress : progress ≤ ticks * 0) :
    progress = 0 := by
  simpa only [Nat.mul_zero, Nat.le_zero] using hprogress

theorem reserve_monotone
    (progress ticks reserve₁ reserve₂ : Nat)
    (hreserve : reserve₁ ≤ reserve₂) :
    progress + ticks * reserve₁ ≤ progress + ticks * reserve₂ := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_left ticks hreserve) progress

theorem reserved_activity_witness :
    3 + 4 * 2 ≤ 4 * (1 + 2) := by
  norm_num

end Viridis.SpeedLimits.ReservedActivity
