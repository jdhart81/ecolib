import Mathlib

/-!
# Re-certifying the Carbon Continuity Threshold: A Lean Proof of the Two-Pool Regenerative Coupling Condition under a Pinned Toolchain

`EcoLib.Restoration.P2CarbonContinuity` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-research` at commit `d77d4365f206`
- `lean/ViridisStatements/P2/CarbonContinuity.lean` (SHA-256 `a5a6e8c63205b865…`)
- `runs/2026-10-29_P2/proofs/P2.CarbonContinuity.lean` (SHA-256 `bfced37f622d1ab9…`)
Certification: ENGINE_V3_VERIFY, evidence `runs/2026-10-29_P2/certification.json`
Engine run: 2026-10-29_P2
Public since: 2026-10-29

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

/-!
# P2 · re-certification: the Carbon Continuity threshold

The live Viridis OS kernel "Carbon Continuity — wildfire recovery threshold diagnostic"
(runtime `viridis.carbon-continuity-threshold.v1`, `src/lib/carbonContinuity.ts` in
viridis-conservation-app) decides whether a two-pool carbon portfolio can be kept from
shrinking across repeated disturbance-recovery cycles. Its formal backing is
`Viridis.CarbonContinuity.carbon_continuity_threshold_iff` in the archived canon release
`releases/2026-08-08/Carbon_Continuity_After_Wildfire` (Zenodo 10.5281/zenodo.21855690,
Lean source sha256 899d3bb1929bac8d1ab6b760caffac428de115489e6fc7c1b2752e0769a77fc1).
Its earlier certificate came from the retired Comparator; this module restates the
theorem as a sealed target so the engine can re-prove it under the pinned toolchain.

Model: one cycle maps a living pool `L` and a durable pool `D` to
`L' = a·L + r·D` and `D' = p·L + d·D`, where `a, d ∈ [0, 1)` are the pools' retention
fractions and `r, p > 0` are the transfer rates between them.

`Statement`: with those parameter ranges, a strictly positive portfolio that no cycle
shrinks (componentwise) exists **exactly when** `(1 − a)(1 − d) ≤ r·p`.
-/

namespace ViridisStatements.P2.CarbonContinuity

/-- Living-pool value after one standardized disturbance-recovery cycle. -/
def stepLiving (a r L D : ℝ) : ℝ := a * L + r * D

/-- Durable-pool value after one standardized disturbance-recovery cycle. -/
def stepDurable (d p L D : ℝ) : ℝ := p * L + d * D

/-- A strictly positive portfolio `(L, D)` that one cycle does not shrink in either pool. -/
def Sustainable (a d r p : ℝ) : Prop :=
  ∃ L D : ℝ, 0 < L ∧ 0 < D ∧ L ≤ stepLiving a r L D ∧ D ≤ stepDurable d p L D

/-- **Sealed target `P2.CarbonContinuity`.** For retention fractions `a, d ∈ [0, 1)` and
positive transfer rates `r, p`, a sustainable portfolio exists exactly at or above the
regenerative coupling threshold `(1 − a)(1 − d) ≤ r·p`. -/
def Statement : Prop :=
  ∀ a d r p : ℝ, 0 ≤ a → a < 1 → 0 ≤ d → d < 1 → 0 < r → 0 < p →
    (Sustainable a d r p ↔ (1 - a) * (1 - d) ≤ r * p)

/-! ## Sanity checks

These pin the meaning of the definitions with concrete numbers. -/

/-- The canon's strict witness: `(a, d, r, p) = (3/5, 4/5, 1/2, 1/5)` with `(L, D) = (1/2, 2/5)`
is above the threshold, holds living carbon exactly and grows durable carbon. -/
example : (1 - (3/5 : ℝ)) * (1 - 4/5) < 1/2 * (1/5) ∧
    stepLiving (3/5) (1/2) (1/2) (2/5) = 1/2 ∧ (2/5 : ℝ) < stepDurable (4/5) (1/5) (1/2) (2/5) := by
  norm_num [stepLiving, stepDurable]

/-- A witness portfolio makes `Sustainable` true at that point. -/
example : Sustainable (3/5) (4/5) (1/2) (1/5) :=
  ⟨1/2, 2/5, by norm_num, by norm_num, by norm_num [stepLiving], by norm_num [stepDurable]⟩

/-- Below the threshold: `(a, d, r, p) = (0, 0, 1/2, 1/2)` gives `(1 − a)(1 − d) = 1 > 1/4 = r·p`. -/
example : ¬ ((1 - (0 : ℝ)) * (1 - 0) ≤ 1/2 * (1/2)) := by norm_num

end ViridisStatements.P2.CarbonContinuity


namespace ViridisStatements.P2.CarbonContinuity.Proof

open ViridisStatements.P2.CarbonContinuity

/-- Sufficiency: above the threshold, the portfolio `(L, D) = (r, 1 - a)` is positive and
holds living carbon exactly while durable carbon does not shrink. -/
theorem sufficient (a d r p : ℝ) (ha1 : a < 1) (hr : 0 < r)
    (h : (1 - a) * (1 - d) ≤ r * p) : Sustainable a d r p := by
  refine ⟨r, 1 - a, hr, by linarith, ?_, ?_⟩
  · simp only [stepLiving]; nlinarith
  · simp only [stepDurable]; nlinarith

/-- Necessity: multiplying the two leakage inequalities `(1 - a) L ≤ r D` and
`(1 - d) D ≤ p L` and cancelling `L D > 0` gives the threshold. -/
theorem necessary (a d r p : ℝ) (ha1 : a < 1) (hd1 : d < 1)
    (hs : Sustainable a d r p) : (1 - a) * (1 - d) ≤ r * p := by
  obtain ⟨L, D, hL, hD, hliv, hdur⟩ := hs
  simp only [stepLiving] at hliv
  simp only [stepDurable] at hdur
  have h1 : (1 - a) * L ≤ r * D := by linarith
  have h2 : (1 - d) * D ≤ p * L := by linarith
  have h3 : ((1 - a) * L) * ((1 - d) * D) ≤ (r * D) * (p * L) :=
    mul_le_mul h1 h2 (by nlinarith) (by nlinarith)
  have h4 : ((1 - a) * (1 - d)) * (L * D) ≤ (r * p) * (L * D) := by linarith
  exact le_of_mul_le_mul_right h4 (mul_pos hL hD)

theorem main : ViridisStatements.P2.CarbonContinuity.Statement := by
  intro a d r p _ ha1 _ hd1 hr _
  exact ⟨necessary a d r p ha1 hd1, sufficient a d r p ha1 hr⟩

end ViridisStatements.P2.CarbonContinuity.Proof
