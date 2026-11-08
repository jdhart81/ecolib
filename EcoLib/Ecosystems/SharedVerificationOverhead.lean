import Mathlib

/-!
# SharedVerificationOverhead

`EcoLib.Ecosystems.SharedVerificationOverhead` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-canon` at commit `d43fad229ded`
- `series/SVON/ViridisRun155.lean` (SHA-256 `4d2ce1821e24f16c…`)
Certification: COMPARATOR_CLOUD, evidence `series/SVON/COMPARATOR_SUMMARY.md`
Engine run: Run-155
Public since: 2026-09-13

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

noncomputable section

namespace Viridis.Ecoservices.SharedVerificationOverhead

def separateCost (fixed v1 v2 : ℝ) : ℝ := (fixed + v1) + (fixed + v2)
def bundledCost (fixed v1 v2 : ℝ) : ℝ := fixed + v1 + v2
def bundledWithInteraction (fixed v1 v2 interaction : ℝ) : ℝ :=
  bundledCost fixed v1 v2 + interaction
def netService (gross fixed v1 v2 : ℝ) : ℝ := gross - bundledCost fixed v1 v2

theorem separate_cost_expansion (fixed v1 v2 : ℝ) :
    separateCost fixed v1 v2 = 2 * fixed + v1 + v2 := by
  unfold separateCost
  ring

theorem bundled_cost_expansion (fixed v1 v2 : ℝ) :
    bundledCost fixed v1 v2 = fixed + v1 + v2 := by
  rfl

theorem shared_verification_saving (fixed v1 v2 : ℝ) :
    separateCost fixed v1 v2 - bundledCost fixed v1 v2 = fixed := by
  unfold separateCost bundledCost
  ring

theorem interaction_adjusted_saving (fixed v1 v2 interaction : ℝ) :
    separateCost fixed v1 v2 - bundledWithInteraction fixed v1 v2 interaction =
      fixed - interaction := by
  unfold separateCost bundledWithInteraction bundledCost
  ring

theorem sharing_strictly_cheaper (fixed v1 v2 interaction : ℝ)
    (h : interaction < fixed) :
    bundledWithInteraction fixed v1 v2 interaction < separateCost fixed v1 v2 := by
  unfold bundledWithInteraction bundledCost separateCost
  linarith

theorem bundled_marginal_floor (fixed epsilon b1 b2 v1 v2 : ℝ)
    (h1 : epsilon * b1 ≤ v1) (h2 : epsilon * b2 ≤ v2) :
    fixed + epsilon * (b1 + b2) ≤ bundledCost fixed v1 v2 := by
  unfold bundledCost
  nlinarith

theorem net_service_nonnegative_iff (gross fixed v1 v2 : ℝ) :
    0 ≤ netService gross fixed v1 v2 ↔ bundledCost fixed v1 v2 ≤ gross := by
  unfold netService
  exact sub_nonneg

theorem shared_verification_witness :
    separateCost 2 3 5 = 12 ∧ bundledCost 2 3 5 = 10 ∧
      separateCost 2 3 5 - bundledCost 2 3 5 = 2 := by
  norm_num [separateCost, bundledCost]

end Viridis.Ecoservices.SharedVerificationOverhead

