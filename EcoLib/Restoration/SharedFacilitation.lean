import Mathlib

/-!
# SharedFacilitation

`EcoLib.Restoration.SharedFacilitation` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-canon` at commit `d43fad229ded`
- `series/SFB/VERIFICATION_CANDIDATE.lean` (SHA-256 `eb55692ff2b129da…`)
Certification: COMPARATOR_CLOUD, evidence `series/SFB/COMPARATOR_SUMMARY.md`
Engine run: Run-149
Public since: 2026-09-01

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

noncomputable section

namespace Viridis.Afforestation.SharedFacilitation

def pooledMargin (demandOne demandTwo supportOne supportTwo : ℝ) : ℝ :=
  (supportOne + supportTwo) - (demandOne + demandTwo)

theorem pooled_margin_identity
    (demandOne demandTwo supportOne supportTwo : ℝ) :
    pooledMargin demandOne demandTwo supportOne supportTwo =
      (supportOne - demandOne) + (supportTwo - demandTwo) := by
  unfold pooledMargin
  ring

theorem pooled_feasible_iff_margin_nonnegative
    (demandOne demandTwo supportOne supportTwo : ℝ) :
    demandOne + demandTwo ≤ supportOne + supportTwo ↔
      0 ≤ pooledMargin demandOne demandTwo supportOne supportTwo := by
  unfold pooledMargin
  constructor <;> intro h <;> linarith

theorem isolated_feasible_implies_pooled
    (demandOne demandTwo supportOne supportTwo : ℝ)
    (hOne : demandOne ≤ supportOne) (hTwo : demandTwo ≤ supportTwo) :
    demandOne + demandTwo ≤ supportOne + supportTwo := by
  linarith

theorem transfer_conserves_pooled_margin
    (demandOne demandTwo supportOne supportTwo transfer : ℝ) :
    pooledMargin demandOne demandTwo (supportOne - transfer) (supportTwo + transfer) =
      pooledMargin demandOne demandTwo supportOne supportTwo := by
  unfold pooledMargin
  ring

theorem full_pool_double_count_identity
    (supportOne supportTwo : ℝ) :
    2 * (supportOne + supportTwo) - (supportOne + supportTwo) =
      supportOne + supportTwo := by
  ring

theorem shared_facilitation_nonvacuous_witness :
    (0 : ℝ) < 3 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 2 ∧
      (3 : ℝ) + 1 ≤ 2 + 2 ∧ ¬ ((3 : ℝ) ≤ 2) ∧
      pooledMargin 3 1 2 2 = 0 := by
  norm_num [pooledMargin]

end Viridis.Afforestation.SharedFacilitation
