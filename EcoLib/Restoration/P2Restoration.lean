import Mathlib

/-!
# Re-certifying the Viridis OS Decision Kernels: A Lean Proof of the Restoration Critical-Nucleus Core

`EcoLib.Restoration.P2Restoration` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-research` at commit `d77d4365f206`
- `lean/ViridisStatements/P2/Restoration.lean` (SHA-256 `fd40b113c06beaed…`)
- `runs/2026-10-31_P2/proofs/P2.Restoration.lean` (SHA-256 `59286948a6b807ac…`)
Certification: ENGINE_V3_VERIFY, evidence `runs/2026-10-31_P2/certification.json`
Engine run: 2026-10-31_P2
Public since: 2026-10-31

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

/-!
# P2 · re-certification: the Restoration critical-nucleus go/no-go

The live Viridis OS Restoration kernel decides whether a planted cluster on degraded land is
large enough to grow into forest (go) or will dissolve back into the degraded state (no-go).
Its formal backing is the Forest Nucleation Theorem clean core,
`Viridis.Afforestation.ForestNucleation.critical_nucleus` and
`Viridis.Afforestation.ForestNucleation.barrier_half_identity`, in the archived canon
(github.com/jdhart81/viridis-canon, commit 80d32904d751b45f415e23f872510cc2eddca3ff,
file `ForestNucleation.lean`, sha256
667a826a2e5befac67964b69670435362de2d3d792e163807c3bb7c2aec28132).
This module restates those two theorems, over the same definitions, as one sealed target.

Model (classical nucleation in the cube-root order parameter `r = n^(1/3)`): a cluster of
`n = r^3` trees has free energy `G(r) = -Δμ·r^3 + a·σ·r^2`, where `Δμ` is the per-tree driving
force, `σ` the edge "surface tension" and `a` a shape factor. The critical radius is
`rStar = 2aσ/(3Δμ)` and the critical nucleus is `n* = rStar^3`.

`Statement`, part 1 (`critical_nucleus`): for `Δμ, a, σ > 0`, `rStar > 0` and `rStar` is the
unique global maximiser of `G` over `r ≥ 0` (the top of the nucleation barrier).
`Statement`, part 2 (`barrier_half_identity`): for `Δμ > 0`, the barrier height is
`G(rStar) = ½·Δμ·rStar^3`, i.e. `ΔG* = ½·Δμ·n*`.
-/

namespace ViridisStatements.P2.Restoration

/-- Critical radius (cube-root order parameter) `rStar = 2aσ/(3Δμ)`;
the critical nucleus is `n* = rStar ^ 3`. -/
noncomputable def rStar (Δμ a σ : ℝ) : ℝ := 2 * a * σ / (3 * Δμ)

/-- Nucleation free energy in the cube-root order parameter `r` (with `n = r^3`,
`n^(2/3) = r^2`): `G(r) = -Δμ·r^3 + a·σ·r^2`. -/
noncomputable def G (Δμ a σ r : ℝ) : ℝ := -Δμ * r ^ 3 + a * σ * r ^ 2

/-- **Sealed target `P2.Restoration`.**
(1) For positive driving force, shape factor and surface tension, the critical radius is
positive and is the unique maximiser of `G` on `r ≥ 0`.
(2) For positive driving force, the barrier height is half the driving energy stored in the
critical nucleus: `G(rStar) = ½·Δμ·rStar^3`. -/
def Statement : Prop :=
  (∀ Δμ a σ : ℝ, 0 < Δμ → 0 < a → 0 < σ →
    0 < rStar Δμ a σ ∧
    (∀ r : ℝ, 0 ≤ r → G Δμ a σ r ≤ G Δμ a σ (rStar Δμ a σ)) ∧
    (∀ r : ℝ, 0 ≤ r → G Δμ a σ r = G Δμ a σ (rStar Δμ a σ) → r = rStar Δμ a σ)) ∧
  (∀ Δμ a σ : ℝ, 0 < Δμ →
    G Δμ a σ (rStar Δμ a σ) = (1 / 2) * Δμ * (rStar Δμ a σ) ^ 3)

/-! ## Sanity checks

These pin the meaning of the definitions with concrete numbers. -/

/-- The canon's non-vacuity witness `(Δμ, a, σ) = (1, 1, 3/2)`: `rStar = 1`, so `n* = 1`,
and the barrier is `G(1) = 1/2 = ½·1·1^3 > 0`. -/
example : rStar 1 1 (3/2) = 1 ∧ G 1 1 (3/2) 1 = 1/2 ∧ (1/2 : ℝ) = (1/2) * 1 * 1 ^ 3 := by
  norm_num [rStar, G]

/-- Below the critical radius the free energy is lower than at the barrier top
(a sub-critical cluster sits on the uphill side): `G(1/2) = 1/4 < 1/2 = G(1)`. -/
example : G 1 1 (3/2) (1/2) = 1/4 ∧ G 1 1 (3/2) (1/2) < G 1 1 (3/2) 1 := by
  norm_num [G]

/-- Above the critical radius the free energy falls again (a super-critical cluster grows
downhill): `G(2) = -2 < 1/2 = G(1)`. -/
example : G 1 1 (3/2) 2 = -2 ∧ G 1 1 (3/2) 2 < G 1 1 (3/2) 1 := by
  norm_num [G]

/-- Negative control: the restriction `r ≥ 0` is needed. At the unphysical `r = -1` the cubic
exceeds the barrier, `G(-1) = 5/2 > 1/2 = G(rStar)`, so maximality fails off `r ≥ 0`. -/
example : G 1 1 (3/2) (rStar 1 1 (3/2)) < G 1 1 (3/2) (-1) := by
  norm_num [G, rStar]

/-- Negative control: the barrier is half, not all, of `Δμ·n*`:
`G(rStar) = 1/2 ≠ 1 = Δμ·rStar^3` at the witness. -/
example : G 1 1 (3/2) (rStar 1 1 (3/2)) ≠ 1 * (rStar 1 1 (3/2)) ^ 3 := by
  norm_num [G, rStar]

/-- Negative control: with negative driving force (`Δμ = -1`, degraded state favoured) the
critical radius is negative, so part 1 genuinely needs `0 < Δμ`. -/
example : rStar (-1) 1 (3/2) < 0 := by
  norm_num [rStar]

end ViridisStatements.P2.Restoration


namespace ViridisStatements.P2.Restoration.Proof

open ViridisStatements.P2.Restoration

/-- The critical radius is positive for positive parameters. -/
lemma rStar_pos (Δμ a σ : ℝ) (hΔμ : 0 < Δμ) (ha : 0 < a) (hσ : 0 < σ) :
    0 < rStar Δμ a σ := by
  unfold rStar
  positivity

/-- `a σ = (3/2) Δμ rStar` whenever `Δμ ≠ 0`. -/
lemma aσ_eq (Δμ a σ : ℝ) (hΔμ : Δμ ≠ 0) :
    a * σ = 3 / 2 * Δμ * rStar Δμ a σ := by
  unfold rStar
  field_simp

/-- Key factorisation: `G(rStar) - G(r) = Δμ (r - rStar)^2 (r + rStar/2)`. -/
lemma key_identity (Δμ a σ r : ℝ) (hΔμ : Δμ ≠ 0) :
    G Δμ a σ (rStar Δμ a σ) - G Δμ a σ r =
      Δμ * (r - rStar Δμ a σ) ^ 2 * (r + rStar Δμ a σ / 2) := by
  unfold G
  rw [aσ_eq Δμ a σ hΔμ]
  ring

/-- Half-barrier identity (holds for any `Δμ`, but stated as in the canon). -/
lemma barrier_half (Δμ a σ : ℝ) (hΔμ : 0 < Δμ) :
    G Δμ a σ (rStar Δμ a σ) = (1 / 2) * Δμ * (rStar Δμ a σ) ^ 3 := by
  unfold G
  rw [aσ_eq Δμ a σ hΔμ.ne']
  ring

theorem critical_nucleus (Δμ a σ : ℝ) (hΔμ : 0 < Δμ) (ha : 0 < a) (hσ : 0 < σ) :
    0 < rStar Δμ a σ ∧
    (∀ r : ℝ, 0 ≤ r → G Δμ a σ r ≤ G Δμ a σ (rStar Δμ a σ)) ∧
    (∀ r : ℝ, 0 ≤ r → G Δμ a σ r = G Δμ a σ (rStar Δμ a σ) → r = rStar Δμ a σ) := by
  have hs := rStar_pos Δμ a σ hΔμ ha hσ
  refine ⟨hs, fun r hr => ?_, fun r hr h => ?_⟩
  · have hk := key_identity Δμ a σ r hΔμ.ne'
    have : 0 ≤ Δμ * (r - rStar Δμ a σ) ^ 2 * (r + rStar Δμ a σ / 2) := by positivity
    linarith
  · have hk := key_identity Δμ a σ r hΔμ.ne'
    rw [h, sub_self] at hk
    have h2 : 0 < r + rStar Δμ a σ / 2 := by positivity
    have h3 : (r - rStar Δμ a σ) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hk.symm with h4 | h4
      · rcases mul_eq_zero.mp h4 with h5 | h5
        · exact absurd h5 hΔμ.ne'
        · exact h5
      · exact absurd h4 h2.ne'
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
    linarith

theorem main : ViridisStatements.P2.Restoration.Statement :=
  ⟨fun Δμ a σ hΔμ ha hσ => critical_nucleus Δμ a σ hΔμ ha hσ,
   fun Δμ a σ hΔμ => barrier_half Δμ a σ hΔμ⟩

end ViridisStatements.P2.Restoration.Proof
