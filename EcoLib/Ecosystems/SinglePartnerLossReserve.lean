import Mathlib

/-!
# SinglePartnerLossReserve

`EcoLib.Ecosystems.SinglePartnerLossReserve` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-canon` at commit `d43fad229ded`
- `series/SPLR/ViridisRun169.lean` (SHA-256 `068492251538894b…`)
Certification: COMPARATOR_CLOUD, evidence `series/SPLR/COMPARATOR_SUMMARY.md`
Engine run: Run-169
Public since: 2026-09-19

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

namespace Viridis.GaianSystems.SinglePartnerLossReserve

def retainedAfterLoss (a b c lost : ℝ) : ℝ := a + b + c - lost

theorem loss_budget_guarantee
    (a b c q budget lost : ℝ)
    (hreserve : q + budget ≤ a + b + c)
    (hloss : lost ≤ budget) :
    q ≤ retainedAfterLoss a b c lost := by
  unfold retainedAfterLoss
  linarith

theorem loss_of_a (a b c q : ℝ) (h : q ≤ b + c) :
    q ≤ retainedAfterLoss a b c a := by
  unfold retainedAfterLoss
  linarith

theorem loss_of_b (a b c q : ℝ) (h : q ≤ a + c) :
    q ≤ retainedAfterLoss a b c b := by
  unfold retainedAfterLoss
  linarith

theorem loss_of_c (a b c q : ℝ) (h : q ≤ a + b) :
    q ≤ retainedAfterLoss a b c c := by
  unfold retainedAfterLoss
  linarith

theorem three_partner_single_loss_guarantee
    (a b c q : ℝ)
    (hab : q ≤ a + b) (hac : q ≤ a + c) (hbc : q ≤ b + c) :
    q ≤ retainedAfterLoss a b c a ∧
    q ≤ retainedAfterLoss a b c b ∧
    q ≤ retainedAfterLoss a b c c := by
  constructor
  · exact loss_of_a a b c q hbc
  · constructor
    · exact loss_of_b a b c q hac
    · exact loss_of_c a b c q hab

theorem reserve_monotone_new_partner
    (a b c d q budget : ℝ)
    (h : q + budget ≤ a + b + c) (hd : 0 ≤ d) :
    q + budget ≤ a + b + c + d := by
  linarith

theorem single_partner_loss_witness :
    retainedAfterLoss 2 3 5 5 = 5 ∧
    retainedAfterLoss 2 3 5 3 = 7 ∧
    retainedAfterLoss 2 3 5 2 = 8 := by
  norm_num [retainedAfterLoss]

theorem concentrated_total_counterexample :
    retainedAfterLoss 5 5 0 5 = 5 ∧
    retainedAfterLoss 4 3 3 4 = 6 := by
  norm_num [retainedAfterLoss]

end Viridis.GaianSystems.SinglePartnerLossReserve

