import Mathlib

/-!
# CheckerAgreement

`EcoLib.Alignment.CheckerAgreement` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-canon` at commit `d43fad229ded`
- `series/CAIA/ViridisRun166.lean` (SHA-256 `668f9abac988a57d…`)
Certification: COMPARATOR_CLOUD, evidence `series/CAIA/COMPARATOR_SUMMARY.md`
Engine run: Run-166
Public since: 2026-09-19

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

namespace Viridis.Computation.CheckerAgreement

theorem disagreement_exposes_error (truth left right : Bool) (h : left ≠ right) :
    left ≠ truth ∨ right ≠ truth := by
  cases truth <;> cases left <;> cases right <;> simp_all

theorem agreement_with_left_soundness (truth left right : Bool)
    (hAgree : left = right) (hLeft : left = truth) : right = truth := by
  calc
    right = left := hAgree.symm
    _ = truth := hLeft

theorem agreement_with_right_soundness (truth left right : Bool)
    (hAgree : left = right) (hRight : right = truth) : left = truth := by
  calc
    left = right := hAgree
    _ = truth := hRight

theorem shared_wrong_agreement_witness :
    ∃ truth left right : Bool, left = right ∧ left ≠ truth ∧ right ≠ truth := by
  exact ⟨false, true, true, rfl, by simp, by simp⟩

end Viridis.Computation.CheckerAgreement
