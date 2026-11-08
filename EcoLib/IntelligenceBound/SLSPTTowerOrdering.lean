import Mathlib

/-!
# Inverse-square shadow-price and capacity planner

`EcoLib.IntelligenceBound.SLSPTTowerOrdering` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-canon` at commit `d43fad229ded`
- `P5_SLSPT/SLSPTTowerOrdering.lean` (SHA-256 `cf15279d012c80cd…`)
Certification: CANON_PUBLISHED_LEAN, evidence `P5_SLSPT/function.json`

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: NOT_VALIDATED.
-/

/-!
# Speed Limit Shadow Price Tower (SLSPT) Ordering Theorems

The SLSPT has shadow prices p_i(σ) = C_i / σ² at four levels.
We prove that the tower ordering is exact, transitive, and that
the gap between levels preserves the quadratic divergence structure.
-/

open Real

/-
Prefactor ordering: C₁ ≤ C₂ iff C₁/σ² ≤ C₂/σ² for any positive σ.
-/
theorem prefactor_ordering (C1 C2 sigma : ℝ)
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hsigma : 0 < sigma) :
    C1 ≤ C2 ↔ C1 / sigma ^ 2 ≤ C2 / sigma ^ 2 := by
  rw [ div_le_div_iff_of_pos_right ( sq_pos_of_pos hsigma ) ]

/-
Strict prefactor ordering: C₁ < C₂ iff C₁/σ² < C₂/σ² for any positive σ.
-/
theorem strict_prefactor_ordering (C1 C2 sigma : ℝ)
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hsigma : 0 < sigma) :
    C1 < C2 ↔ C1 / sigma ^ 2 < C2 / sigma ^ 2 := by
  rw [ div_lt_div_iff_of_pos_right ( sq_pos_of_pos hsigma ) ]

/-
Transitivity of tower ordering at fixed σ.
-/
theorem tower_ordering_trans (C1 C2 C3 sigma : ℝ)
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hC3 : 0 < C3) (hsigma : 0 < sigma) :
    C1 / sigma ^ 2 ≤ C2 / sigma ^ 2 →
    C2 / sigma ^ 2 ≤ C3 / sigma ^ 2 →
    C1 / sigma ^ 2 ≤ C3 / sigma ^ 2 := by
  grind

/-
Level-curve ordering: √(C₁/M) < √(C₂/M) when C₁ < C₂ and M > 0.
-/
theorem level_curve_ordering (C1 C2 M : ℝ)
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hM : 0 < M) (hlt : C1 < C2) :
    Real.sqrt (C1 / M) < Real.sqrt (C2 / M) := by
  gcongr

/-
Cross-level shadow price gap preserves quadratic structure.
-/
theorem cross_level_gap (C1 C2 sigma : ℝ)
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hsigma : 0 < sigma) (hlt : C1 < C2) :
    ∀ epsilon : ℝ, 0 < epsilon →
    C2 / sigma ^ 2 - C1 / sigma ^ 2 = (C2 - C1) / sigma ^ 2 := by
  exact fun _ _ => by ring;
