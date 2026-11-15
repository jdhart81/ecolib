import Mathlib

/-!
# Loop Mass Balance for a Single-Material Recovery Loop: A Lean Proof

`EcoLib.Foundations.P3LoopMassBalance` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-research` at commit `77f077a14655`
- `lean/ViridisStatements/P3/LoopMassBalance.lean` (SHA-256 `f00634594133f7ed…`)
- `runs/2026-11-15_P3/proofs/P3.LoopMassBalance.lean` (SHA-256 `0e110da9753e7146…`)
Certification: ENGINE_V3_VERIFY, evidence `runs/2026-11-15_P3/certification.json`
Engine run: 2026-11-15_P3
Public since: 2026-11-15

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

/-!
# P3 · Loop mass balance for a single-material recovery loop

Model (one material, discrete periods `t = 0, 1, 2, …`):

* demand per period `D ≥ 0`;
* recovery fraction `r ∈ [0, 1]`: the share of each period's demand met from recovered
  (secondary) material, so the virgin input per period is `V = D·(1 - r)`;
* stock retention `ρ ∈ [0, 1)`: the share of the secondary stock that survives one period;
* secondary stock `S(t+1) = ρ·S(t) + r·D`, starting from an arbitrary `S(0)`;
* steady stock `S* = r·D / (1 - ρ)`;
* cumulative virgin input over `T` periods: the sum of `V` over periods `0, …, T-1`.

`Statement` (for every `D ≥ 0`, `r ∈ [0,1]`, `ρ ∈ [0,1)`, `S(0)`):
1. `0 ≤ V ≤ D`;
2. closed form: `S(t) - S* = ρ^t · (S(0) - S*)` for every `t`;
3. convergence: `S(t) → S*` as `t → ∞`;
4. cumulative virgin input over `T` periods equals `T·D·(1 - r)`;
and, for `D > 0` and `T > 0`, cumulative virgin input is strictly decreasing in `r` on `[0,1]`.

The statement fixes the arithmetic of the model only. It makes no claim about any real
recovery rate, retention rate, demand or material.
-/

noncomputable section

namespace ViridisStatements.P3.LoopMassBalance

open Filter Topology

/-- Virgin input per period: demand not met by recovered material, `V = D·(1 - r)`. -/
def virgin (D r : ℝ) : ℝ := D * (1 - r)

/-- Secondary stock: `S(0) = S0`, `S(t+1) = ρ·S(t) + r·D`. -/
def stock (ρ r D S0 : ℝ) : ℕ → ℝ
  | 0 => S0
  | t + 1 => ρ * stock ρ r D S0 t + r * D

/-- Steady secondary stock `S* = r·D / (1 - ρ)`. -/
def steadyStock (ρ r D : ℝ) : ℝ := r * D / (1 - ρ)

/-- Cumulative virgin input over periods `0, …, T-1`. -/
def cumulativeVirgin (D r : ℝ) (T : ℕ) : ℝ := ∑ _t ∈ Finset.range T, virgin D r

/-- **Proposed sealed target `P3.LoopMassBalance`.** -/
def Statement : Prop :=
  (∀ D r ρ S0 : ℝ, 0 ≤ D → 0 ≤ r → r ≤ 1 → 0 ≤ ρ → ρ < 1 →
    (0 ≤ virgin D r ∧ virgin D r ≤ D) ∧
    (∀ t : ℕ, stock ρ r D S0 t - steadyStock ρ r D
        = ρ ^ t * (S0 - steadyStock ρ r D)) ∧
    Tendsto (stock ρ r D S0) atTop (𝓝 (steadyStock ρ r D)) ∧
    (∀ T : ℕ, cumulativeVirgin D r T = (T : ℝ) * D * (1 - r))) ∧
  (∀ (D : ℝ) (T : ℕ), 0 < D → 0 < T →
    StrictAntiOn (fun r => cumulativeVirgin D r T) (Set.Icc 0 1))

/-! ## Sanity checks -/

/-- Witness `D = 10`, `r = 1/2`, `ρ = 1/2`, `S(0) = 0`: virgin input `5` per period, the stock
runs `0, 5, 15/2, …` towards `S* = 10`, and the gap halves each period:
`S(2) - S* = -5/2 = (1/2)^2 · (0 - 10)`. -/
example : virgin 10 (1/2) = 5 ∧ stock (1/2) (1/2) 10 0 1 = 5 ∧
    stock (1/2) (1/2) 10 0 2 = 15/2 ∧ steadyStock (1/2) (1/2) 10 = 10 ∧
    stock (1/2) (1/2) 10 0 2 - steadyStock (1/2) (1/2) 10
      = (1/2 : ℝ) ^ 2 * (0 - steadyStock (1/2) (1/2) 10) := by
  norm_num [virgin, stock, steadyStock]

/-- Cumulative virgin input at the witness over `T = 3` periods: `3·10·(1/2) = 15`. -/
example : cumulativeVirgin 10 (1/2) 3 = 15 := by
  norm_num [cumulativeVirgin, virgin, Finset.sum_range_succ]

/-- Raising recovery from `1/2` to `3/4` lowers the 3-period virgin total from `15` to `15/2`. -/
example : cumulativeVirgin 10 (3/4) 3 < cumulativeVirgin 10 (1/2) 3 := by
  norm_num [cumulativeVirgin, virgin, Finset.sum_range_succ]

/-- Negative control: `ρ < 1` is needed. With full retention `ρ = 1` the stock grows without
bound (`S(3) = 3` for `r = D = 1`, `S(0) = 0`), while the formula `r·D/(1-ρ)` divides by zero
and Lean returns `0`; the closed form fails at `t = 1`. -/
example : stock 1 1 1 0 3 = 3 ∧ steadyStock 1 1 1 = 0 ∧
    stock 1 1 1 0 1 - steadyStock 1 1 1 ≠ (1 : ℝ) ^ 1 * (0 - steadyStock 1 1 1) := by
  norm_num [stock, steadyStock]

/-- Negative control: `D > 0` is needed for strictness. With zero demand the virgin total is
`0` at every recovery fraction. -/
example : cumulativeVirgin 0 0 3 = cumulativeVirgin 0 1 3 := by
  norm_num [cumulativeVirgin, virgin]

/-- Negative control: `r ≤ 1` is needed for `V ≥ 0`; an out-of-range "recovery" `r = 2`
gives negative virgin input. -/
example : virgin 10 2 < 0 := by
  norm_num [virgin]

end ViridisStatements.P3.LoopMassBalance


namespace ViridisStatements.P3.LoopMassBalance.Proof

open Filter Topology
open ViridisStatements.P3.LoopMassBalance

/-- One-step gap recursion: `S(t+1) - S* = ρ · (S(t) - S*)`. -/
theorem gap_succ (ρ r D S0 : ℝ) (hρ : ρ < 1) (t : ℕ) :
    stock ρ r D S0 (t + 1) - steadyStock ρ r D
      = ρ * (stock ρ r D S0 t - steadyStock ρ r D) := by
  have h : (1 - ρ) ≠ 0 := by linarith
  simp only [stock, steadyStock]
  field_simp
  ring

/-- Closed form of the stock gap. -/
theorem gap_closed (ρ r D S0 : ℝ) (hρ : ρ < 1) (t : ℕ) :
    stock ρ r D S0 t - steadyStock ρ r D = ρ ^ t * (S0 - steadyStock ρ r D) := by
  induction t with
  | zero => simp [stock]
  | succ n ih => rw [gap_succ ρ r D S0 hρ, ih, pow_succ]; ring

/-- Cumulative virgin input equals `T·D·(1 - r)`. -/
theorem cumulative_eq (D r : ℝ) (T : ℕ) :
    cumulativeVirgin D r T = (T : ℝ) * D * (1 - r) := by
  simp [cumulativeVirgin, virgin, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Convergence of the stock to the steady stock. -/
theorem stock_tendsto (ρ r D S0 : ℝ) (h0 : 0 ≤ ρ) (hρ : ρ < 1) :
    Tendsto (stock ρ r D S0) atTop (𝓝 (steadyStock ρ r D)) := by
  have hp : Tendsto (fun t : ℕ => ρ ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0 hρ
  have hg : Tendsto (fun t : ℕ => ρ ^ t * (S0 - steadyStock ρ r D) + steadyStock ρ r D)
      atTop (𝓝 (0 * (S0 - steadyStock ρ r D) + steadyStock ρ r D)) :=
    (hp.mul_const _).add_const _
  rw [zero_mul, zero_add] at hg
  refine hg.congr' (Eventually.of_forall fun t => ?_)
  have := gap_closed ρ r D S0 hρ t
  linarith

theorem main : ViridisStatements.P3.LoopMassBalance.Statement := by
  refine ⟨?_, ?_⟩
  · intro D r ρ S0 hD hr0 hr1 hρ0 hρ1
    refine ⟨⟨?_, ?_⟩, gap_closed ρ r D S0 hρ1, stock_tendsto ρ r D S0 hρ0 hρ1,
      cumulative_eq D r⟩
    · unfold virgin; exact mul_nonneg hD (by linarith)
    · unfold virgin; nlinarith
  · intro D T hD hT a _ b _ hab
    simp only [cumulative_eq]
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    have : 0 < (T : ℝ) * D := mul_pos hT' hD
    nlinarith

end ViridisStatements.P3.LoopMassBalance.Proof
