import Mathlib

/-!
# JointMinimumFloor

`EcoLib.Ecosystems.JointMinimumFloor` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-canon` at commit `d43fad229ded`
- `series/JMSF/ViridisRun174.lean` (SHA-256 `5914ede7a3ee10ca…`)
Certification: COMPARATOR_CLOUD, evidence `series/JMSF/COMPARATOR_SUMMARY.md`
Engine run: Run-174
Public since: 2026-09-27

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

namespace Viridis.Ecoservices.JointMinimumFloor

theorem joint_floor_iff
    (a b x : Nat) :
    max a b ≤ x ↔ a ≤ x ∧ b ≤ x := by
  exact max_le_iff

theorem joint_floor_dominates_left
    (a b : Nat) :
    a ≤ max a b := by
  exact le_max_left a b

theorem joint_floor_dominates_right
    (a b : Nat) :
    b ≤ max a b := by
  exact le_max_right a b

theorem agreed_floor_sufficient
    (a b x : Nat) (ha : a ≤ x) (hb : b ≤ x) :
    max a b ≤ x := by
  exact max_le ha hb

theorem joint_floor_witness :
    max 3 5 ≤ 7 := by
  norm_num

end Viridis.Ecoservices.JointMinimumFloor
