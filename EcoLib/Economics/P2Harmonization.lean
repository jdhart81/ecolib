import Mathlib

/-!
# Re-certifying the Viridis OS Decision Kernels: A Lean Proof of the Harmonization Scalar-Price Welfare Core

`EcoLib.Economics.P2Harmonization` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-research` at commit `d77d4365f206`
- `lean/ViridisStatements/P2/Harmonization.lean` (SHA-256 `48934ecb301f858b…`)
- `runs/2026-11-02_P2/proofs/P2.Harmonization.lean` (SHA-256 `1bcfdf8580578e7a…`)
Certification: ENGINE_V3_VERIFY, evidence `runs/2026-11-02_P2/certification.json`
Engine run: 2026-11-02_P2
Public since: 2026-11-02

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

/-!
# P2 · re-certification: Gaian Harmonization, the scalar-price welfare theorem

The live Viridis OS Harmonization kernel coordinates `N` local stewards (sites, agents) toward
a shared regulation target by broadcasting one scalar price instead of `N` commands. Its formal
backing is the Gaian Harmonization Theorem clean core,
`Viridis.Gaian.GaianHarmonization.ght_market_clears` and
`Viridis.Gaian.GaianHarmonization.ght_strong_duality_decentralized_eq_centralized`, in the
archived canon (github.com/jdhart81/viridis-canon, commit
80d32904d751b45f415e23f872510cc2eddca3ff, file `GaianHarmonization.lean`, sha256
cfdead658b1373cd311ac816f88867c5fd429a708e813a23a3293c901d110aec).
This module restates those two theorems, over the same definitions, as one sealed target.

Model: agent `i` chooses effort `x i` with local dissipation `(a i / 2)·(x i − b i)^2`
(curvature `a i > 0`, ideal effort `b i`); the planet requires `∑ i, x i = X`. At broadcast
price `lam` agent `i`'s best response is `br lam i = b i − lam / a i`. The clearing price is
`lamStar = (∑ b − X) / (∑ 1/a)` and `xStar i = br lamStar i`.

`Statement`: for `N > 0` agents with positive curvatures and any target `X`,
(1) the clearing price makes the aggregate best response meet the target exactly, and
(2) the induced allocation has no greater total dissipation than any feasible allocation.
-/

namespace ViridisStatements.P2.Harmonization

open scoped BigOperators

/-- Agent `i`'s price-taking best response to broadcast price `lam`: the minimiser of its
private Lagrangian `(a i / 2)·(x − b i)^2 + lam·x`. -/
noncomputable def br {N : ℕ} (a b : Fin N → ℝ) (lam : ℝ) (i : Fin N) : ℝ :=
  b i - lam / a i

/-- Centralised planetary dissipation `J(x) = ∑ i, (a i / 2)·(x i − b i)^2`. -/
noncomputable def J {N : ℕ} (a b : Fin N → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ i, (a i / 2) * (x i - b i) ^ 2

/-- The market-clearing (shadow) price `lamStar = (∑ b − X) / (∑ 1/a)`. -/
noncomputable def lamStar {N : ℕ} (a b : Fin N → ℝ) (X : ℝ) : ℝ :=
  (∑ i, b i - X) / (∑ i, 1 / a i)

/-- The decentralised allocation: every agent best-responds to the clearing price. -/
noncomputable def xStar {N : ℕ} (a b : Fin N → ℝ) (X : ℝ) (i : Fin N) : ℝ :=
  br a b (lamStar a b X) i

/-- **Sealed target `P2.Harmonization`.** For `N > 0` agents with positive curvatures and any
target `X`: (1) market clearing, `∑ i, br (lamStar) i = X`; (2) strong duality, every
allocation `y` with `∑ i, y i = X` satisfies `J xStar ≤ J y`. -/
def Statement : Prop :=
  ∀ (N : ℕ) (a b : Fin N → ℝ), 0 < N → (∀ i, 0 < a i) → ∀ X : ℝ,
    (∑ i, br a b (lamStar a b X) i) = X ∧
    (∀ y : Fin N → ℝ, (∑ i, y i) = X → J a b (xStar a b X) ≤ J a b y)

/-! ## Sanity checks

These pin the meaning of the definitions with concrete numbers, on the canon's non-vacuity
instance `N = 2`, `a = (1, 1)`, `b = (1, 1)`, `X = 0`. -/

/-- The clearing price is `lamStar = (2 − 0)/(1 + 1) = 1`. -/
example : lamStar (N := 2) ![1, 1] ![1, 1] 0 = 1 := by
  norm_num [lamStar, Fin.sum_univ_two]

/-- Each agent best-responds with `xStar i = 1 − 1/1 = 0`; the target binds (`xStar 0 ≠ b 0`),
the allocation is feasible (`0 + 0 = 0`) and its dissipation is `J xStar = 1/2 + 1/2 = 1`. -/
example : xStar (N := 2) ![1, 1] ![1, 1] 0 0 = 0 ∧ xStar (N := 2) ![1, 1] ![1, 1] 0 1 = 0 ∧
    xStar (N := 2) ![1, 1] ![1, 1] 0 0 ≠ (![1, 1] : Fin 2 → ℝ) 0 ∧
    J (N := 2) ![1, 1] ![1, 1] (xStar ![1, 1] ![1, 1] 0) = 1 := by
  norm_num [xStar, br, lamStar, J, Fin.sum_univ_two]

/-- A different feasible allocation `y = (1, −1)` dissipates more: `J y = 0 + 2 = 2 > 1`. -/
example : J (N := 2) ![1, 1] ![1, 1] ![1, -1] = 2 ∧
    J (N := 2) ![1, 1] ![1, 1] (xStar ![1, 1] ![1, 1] 0) < J (N := 2) ![1, 1] ![1, 1] ![1, -1] := by
  norm_num [xStar, br, lamStar, J, Fin.sum_univ_two]

/-- Negative control: the feasibility hypothesis `∑ y = X` is needed. The infeasible ideal
`y = b = (1, 1)` (sum `2 ≠ 0`) has `J y = 0 < 1 = J xStar`. -/
example : (∑ i, (![1, 1] : Fin 2 → ℝ) i) ≠ 0 ∧
    J (N := 2) ![1, 1] ![1, 1] ![1, 1] < J (N := 2) ![1, 1] ![1, 1] (xStar ![1, 1] ![1, 1] 0) := by
  norm_num [xStar, br, lamStar, J, Fin.sum_univ_two]

/-- Negative control: a wrong price does not clear. At `lam = 0` agents play their ideals and
the aggregate `1 + 1 = 2` misses the target `X = 0`. -/
example : (∑ i, br (N := 2) ![1, 1] ![1, 1] 0 i) ≠ 0 := by
  norm_num [br, Fin.sum_univ_two]

/-- Negative control: the hypothesis `0 < N` is needed. With no agents the aggregate best
response is the empty sum `0`, which misses the target `X = 1`. -/
example : (∑ i, br (N := 0) ![] ![] (lamStar ![] ![] 1) i) ≠ 1 := by
  simp

end ViridisStatements.P2.Harmonization


namespace ViridisStatements.P2.Harmonization.Proof

open ViridisStatements.P2.Harmonization

/-- The sum of reciprocal curvatures is positive when `N > 0` and all `a i > 0`. -/
theorem sum_inv_pos {N : ℕ} (a : Fin N → ℝ) (hN : 0 < N) (ha : ∀ i, 0 < a i) :
    0 < ∑ i, 1 / a i :=
  Finset.sum_pos (fun i _ => one_div_pos.mpr (ha i)) ⟨⟨0, hN⟩, Finset.mem_univ _⟩

/-- Aggregate best response is linear in the price: `∑ br lam = ∑ b − lam · ∑ 1/a`. -/
theorem sum_br {N : ℕ} (a b : Fin N → ℝ) (lam : ℝ) :
    (∑ i, br a b lam i) = (∑ i, b i) - lam * ∑ i, 1 / a i := by
  unfold br
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_one_div]

/-- Market clearing (canon `ght_market_clears`). -/
theorem market_clears {N : ℕ} (a b : Fin N → ℝ) (hN : 0 < N) (ha : ∀ i, 0 < a i) (X : ℝ) :
    (∑ i, br a b (lamStar a b X) i) = X := by
  rw [sum_br]
  unfold lamStar
  rw [div_mul_cancel₀ _ (sum_inv_pos a hN ha).ne']
  ring

/-- Equimarginal principle (canon `ght_equimarginal`): `a i · (xStar i − b i) = −lamStar`. -/
theorem equimarginal {N : ℕ} (a b : Fin N → ℝ) (ha : ∀ i, 0 < a i) (X : ℝ) (i : Fin N) :
    a i * (xStar a b X i - b i) = - lamStar a b X := by
  unfold xStar br
  field_simp [(ha i).ne']
  ring

/-- Pointwise supporting-line inequality for one agent's quadratic dissipation. -/
theorem pointwise {N : ℕ} (a b : Fin N → ℝ) (ha : ∀ i, 0 < a i) (X : ℝ) (y : Fin N → ℝ)
    (i : Fin N) :
    (a i / 2) * (xStar a b X i - b i) ^ 2 + (- lamStar a b X) * (y i - xStar a b X i)
      ≤ (a i / 2) * (y i - b i) ^ 2 := by
  rw [← equimarginal a b ha X i]
  nlinarith [mul_nonneg (ha i).le (sq_nonneg (y i - xStar a b X i))]

/-- Strong duality / welfare theorem (canon
`ght_strong_duality_decentralized_eq_centralized`). -/
theorem strong_duality {N : ℕ} (a b : Fin N → ℝ) (hN : 0 < N) (ha : ∀ i, 0 < a i) (X : ℝ)
    (y : Fin N → ℝ) (hy : (∑ i, y i) = X) :
    J a b (xStar a b X) ≤ J a b y := by
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => pointwise a b ha X y i
  have hx : (∑ i, xStar a b X i) = X := market_clears a b hN ha X
  have hzero : (∑ i, (- lamStar a b X) * (y i - xStar a b X i)) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hy, hx, sub_self, mul_zero]
  rw [Finset.sum_add_distrib, hzero, add_zero] at hsum
  exact hsum

theorem main : ViridisStatements.P2.Harmonization.Statement := by
  intro N a b hN ha X
  exact ⟨market_clears a b hN ha X, fun y hy => strong_duality a b hN ha X y hy⟩

end ViridisStatements.P2.Harmonization.Proof
