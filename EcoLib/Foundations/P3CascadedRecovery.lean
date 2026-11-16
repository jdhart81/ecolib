import Mathlib

/-!
# Cascaded Recovery Bounds: A Lean Proof that a Cascade of Imperfect Stages Beats Each of Its Stages

`EcoLib.Foundations.P3CascadedRecovery` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-research` at commit `b44e36a044bb`
- `lean/ViridisStatements/P3/CascadedRecovery.lean` (SHA-256 `a4e3f3c269b81a1d…`)
- `runs/2026-11-16_P3/proofs/P3.CascadedRecovery.lean` (SHA-256 `eaafbaaa17a78083…`)
Certification: ENGINE_V3_VERIFY, evidence `runs/2026-11-16_P3/certification.json`
Engine run: 2026-11-16_P3
Public since: 2026-11-16

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

/-!
# P3 · Cascaded recovery: virgin share after `n` recovery stages

Model: a material stream passes through `n` recovery stages in series. Stage `i` recovers the
fraction `r i ∈ [0, 1]` of what reaches it, so the fraction that passes it unrecovered is
`1 - r i`. The share of the original stream that still has to be met by virgin material after
the cascade (the *virgin share*) is the product `∏ i, (1 - r i)`.

`Statement` (for every `n` and every `r : Fin n → ℝ` with all `r i ∈ [0, 1]`):
1. `0 ≤ ∏ (1 - r i) ≤ 1`;
2. for every uniform upper bound `m` with `r i ≤ m ≤ 1`: `(1 - m)^n ≤ ∏ (1 - r i)`;
   in particular `(1 - max_i r i)^n ≤ ∏ (1 - r i)`, where the maximum is `⨆ i, r i`;
3. for every stage `j`: `∏ (1 - r i) ≤ 1 - r j` (the cascade is never worse than any one stage);
4. strictness: if `j` has `r j < 1` and some *other* stage `k ≠ j` has `r k > 0`, then
   `∏ (1 - r i) < 1 - r j`.

For `n = 0` the maximum `⨆ i, r i` over the empty type is `0` in Mathlib's conditionally
complete lattice `ℝ`, and both sides of part 2 equal `1`.

No claim is made about any real recovery rate or material.
-/

namespace ViridisStatements.P3.CascadedRecovery

/-- Virgin share after a cascade of `n` stages with recovery fractions `r`. -/
def virginShare {n : ℕ} (r : Fin n → ℝ) : ℝ := ∏ i, (1 - r i)

/-- **Proposed sealed target `P3.CascadedRecovery`.** -/
def Statement : Prop :=
  ∀ (n : ℕ) (r : Fin n → ℝ), (∀ i, 0 ≤ r i) → (∀ i, r i ≤ 1) →
    (0 ≤ virginShare r ∧ virginShare r ≤ 1) ∧
    (∀ m : ℝ, (∀ i, r i ≤ m) → m ≤ 1 → (1 - m) ^ n ≤ virginShare r) ∧
    (1 - ⨆ i, r i) ^ n ≤ virginShare r ∧
    (∀ j, virginShare r ≤ 1 - r j) ∧
    (∀ j k, k ≠ j → 0 < r k → r j < 1 → virginShare r < 1 - r j)

/-! ## Sanity checks -/

/-- Two stages recovering one half each leave a virgin share of `1/4`, which lies between the
lower bound `(1 - 1/2)^2 = 1/4` and the single-stage share `1/2`, strictly below the latter. -/
example : virginShare ![(1/2 : ℝ), 1/2] = 1/4 ∧ (1 - (1/2 : ℝ)) ^ 2 ≤ 1/4 ∧
    virginShare ![(1/2 : ℝ), 1/2] < 1 - 1/2 := by
  norm_num [virginShare, Fin.prod_univ_two]

/-- Three heterogeneous stages `1/2, 1/4, 0`: share `3/8`, above `(1 - 1/2)^3 = 1/8`. -/
example : virginShare ![(1/2 : ℝ), 1/4, 0] = 3/8 ∧
    (1 - (1/2 : ℝ)) ^ 3 < virginShare ![(1/2 : ℝ), 1/4, 0] := by
  simp only [virginShare, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  norm_num

/-- Negative control for strictness: if every *other* stage recovers nothing, the cascade
equals the single stage, so part 4 genuinely needs some `r k > 0` with `k ≠ j`. -/
example : virginShare ![(0 : ℝ), 1/2] = 1 - 1/2 := by
  norm_num [virginShare, Fin.prod_univ_two]

/-- Negative control for strictness: if stage `j` recovers everything (`r j = 1`) the share is
`0 = 1 - r j`, so part 4 genuinely needs `r j < 1`. -/
example : virginShare ![(1/2 : ℝ), 1] = 1 - 1 := by
  norm_num [virginShare, Fin.prod_univ_two]

/-- Negative control: `r i ≤ 1` is needed. An out-of-range stage `r = 2` makes the
"virgin share" negative. -/
example : virginShare ![(2 : ℝ), 1/2] < 0 := by
  norm_num [virginShare, Fin.prod_univ_two]

/-- Negative control: `0 ≤ r i` is needed for part 3. A "stage" with `r = -1` (one that adds
demand) pushes the share above the other stage's share. -/
example : 1 - (1/2 : ℝ) < virginShare ![(-1 : ℝ), 1/2] := by
  norm_num [virginShare, Fin.prod_univ_two]

end ViridisStatements.P3.CascadedRecovery


namespace ViridisStatements.P3.CascadedRecovery.Proof

open ViridisStatements.P3.CascadedRecovery

/-- Every factor `1 - r i` lies in `[0, 1]`. -/
theorem factor_nonneg {n : ℕ} (r : Fin n → ℝ) (h1 : ∀ i, r i ≤ 1) (i : Fin n) :
    0 ≤ 1 - r i := by linarith [h1 i]

theorem factor_le_one {n : ℕ} (r : Fin n → ℝ) (h0 : ∀ i, 0 ≤ r i) (i : Fin n) :
    1 - r i ≤ 1 := by linarith [h0 i]

/-- Any sub-product of the factors lies in `[0, 1]`. -/
theorem subprod_le_one {n : ℕ} (r : Fin n → ℝ) (h0 : ∀ i, 0 ≤ r i) (h1 : ∀ i, r i ≤ 1)
    (s : Finset (Fin n)) : ∏ i ∈ s, (1 - r i) ≤ 1 :=
  Finset.prod_le_one (fun i _ => factor_nonneg r h1 i) (fun i _ => factor_le_one r h0 i)

theorem subprod_nonneg {n : ℕ} (r : Fin n → ℝ) (h1 : ∀ i, r i ≤ 1)
    (s : Finset (Fin n)) : 0 ≤ ∏ i ∈ s, (1 - r i) :=
  Finset.prod_nonneg (fun i _ => factor_nonneg r h1 i)

/-- Splitting off stage `j`: `virginShare r = (1 - r j) · ∏_{i ≠ j} (1 - r i)`. -/
theorem split {n : ℕ} (r : Fin n → ℝ) (j : Fin n) :
    virginShare r = (1 - r j) * ∏ i ∈ Finset.univ.erase j, (1 - r i) :=
  (Finset.mul_prod_erase Finset.univ (fun i => 1 - r i) (Finset.mem_univ j)).symm

/-- Uniform lower bound `(1 - m)^n ≤ virginShare r`. -/
theorem lower_bound {n : ℕ} (r : Fin n → ℝ) (m : ℝ) (hm : ∀ i, r i ≤ m) (hm1 : m ≤ 1) :
    (1 - m) ^ n ≤ virginShare r := by
  have hc : (1 - m) ^ n = ∏ _i : Fin n, (1 - m) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hc, virginShare]
  exact Finset.prod_le_prod (fun _ _ => by linarith) (fun i _ => by linarith [hm i])

theorem main : ViridisStatements.P3.CascadedRecovery.Statement := by
  intro n r h0 h1
  refine ⟨⟨subprod_nonneg r h1 _, subprod_le_one r h0 h1 _⟩,
    fun m hm hm1 => lower_bound r m hm hm1, ?_, ?_, ?_⟩
  · -- the supremum bound
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [virginShare]
    · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      have hbdd : BddAbove (Set.range r) := (Set.finite_range r).bddAbove
      exact lower_bound r _ (fun i => le_ciSup hbdd i) (ciSup_le h1)
  · intro j
    rw [split r j]
    have hP := subprod_le_one r h0 h1 (Finset.univ.erase j)
    have hj := factor_nonneg r h1 j
    nlinarith
  · intro j k hkj hk hj
    rw [split r j]
    have hkmem : k ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩
    have hsplit := Finset.mul_prod_erase (Finset.univ.erase j) (fun i => 1 - r i) hkmem
    have hQ := subprod_le_one r h0 h1 ((Finset.univ.erase j).erase k)
    have hQ0 := subprod_nonneg r h1 ((Finset.univ.erase j).erase k)
    have hP : ∏ i ∈ Finset.univ.erase j, (1 - r i) < 1 := by
      rw [← hsplit]
      have hk1 := factor_nonneg r h1 k
      nlinarith
    have hj' : 0 < 1 - r j := by linarith
    nlinarith

end ViridisStatements.P3.CascadedRecovery.Proof
