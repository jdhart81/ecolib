import Mathlib

/-!
# A Correction Note on Two Early Intelligence Bound Sources: The Unrestricted Axiom Is False, and "No Finite Compensation" Proves Finite Compensation

`EcoLib.IntelligenceBound.P5CompensationUnderCeiling` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-research` at commit `5e698b3b8b4e`
- `lean/ViridisStatements/P5/CompensationUnderCeiling.lean` (SHA-256 `ff09ca9eb882869d…`)
- `runs/2026-11-19_P5/proofs/P5.CompensationUnderCeiling.lean` (SHA-256 `f45607f8fb00d673…`)
Certification: ENGINE_V3_VERIFY, evidence `runs/2026-11-19_P5/certification.json`
Engine run: 2026-11-19_P5
Public since: 2026-11-19

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
The Intelligence Bound (dI/dt <= P*D/(k_B T ln 2)) is a conjecture. Theorems here take its physical premise (a Landauer-type cost) as a hypothesis or definition; solving them proves nothing about the conjecture itself.
-/

/-!
# P5 · Compensation under a power ceiling

`Non_Substitutability_Complete.lean` (SHA-256 `8b1194634…bee273`) introduces a theorem named
`no_finite_compensation` with prose saying no finite power increase compensates a loss of `D`,
but its formal text proves that the finite power `P + P·ΔD/(D − ΔD) = P·D/(D − ΔD)` restores the
bound exactly. This module separates the four facts that the prose mixes, for the capacity
algebra `cap P D C = P · D / C` restated over Mathlib only.

`Statement` is the conjunction of:
1. (interior) for `0 < C`, `0 < P`, `0 < dD < D`, the power `P·D/(D − dD)` restores the
   capacity after the loss, and it is the only power that does;
2. (ceiling) if moreover `P ≤ Pmax`, then some power `P' ≤ Pmax` restores the capacity iff
   `dD ≤ D·(1 − P/Pmax)`;
3. (divergence) for `0 < C, P, D`, the compensating power `P·D/(D − dD)` exceeds any bound `M`
   once `dD < D` is close enough to `D`;
4. (complete loss) for `0 < C, P, D`, at `D = 0` every power gives capacity `0`, strictly below
   `cap P D C`; so no power restores a positive capacity.

The result is elementary; it is a correction, not a new theorem. It says nothing about whether
any agent preserves biodiversity, and nothing about the Intelligence Bound as a physical
conjecture.
-/

noncomputable section

namespace ViridisStatements.P5.CompensationUnderCeiling

/-- Capacity `P · D / C` at power `P`, diversity fraction `D` and per-bit cost `C`. -/
def cap (P D C : ℝ) : ℝ := P * D / C

/-- **Proposed sealed target `P5.CompensationUnderCeiling`.** -/
def Statement : Prop :=
  -- 1. Interior: finite compensation exists and is unique.
  (∀ P D dD C : ℝ, 0 < C → 0 < P → 0 < dD → dD < D →
    cap (P * D / (D - dD)) (D - dD) C = cap P D C ∧
    ∀ P' : ℝ, cap P' (D - dD) C = cap P D C → P' = P * D / (D - dD)) ∧
  -- 2. Ceiling: compensation within `Pmax` is possible exactly when `dD ≤ D·(1 − P/Pmax)`.
  (∀ P D dD C Pmax : ℝ, 0 < C → 0 < P → 0 < dD → dD < D → P ≤ Pmax →
    ((∃ P' : ℝ, P' ≤ Pmax ∧ cap P' (D - dD) C = cap P D C) ↔ dD ≤ D * (1 - P / Pmax))) ∧
  -- 3. Divergence: the compensating power is unbounded as `dD → D⁻`.
  (∀ P D C : ℝ, 0 < C → 0 < P → 0 < D →
    ∀ M : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ dD : ℝ, D - δ < dD → dD < D → M < P * D / (D - dD)) ∧
  -- 4. Complete loss: at `D = 0` no power restores a positive capacity.
  (∀ P D C : ℝ, 0 < C → 0 < P → 0 < D →
    ∀ P' : ℝ, cap P' 0 C = 0 ∧ cap P' 0 C < cap P D C)

/-! ## Sanity checks -/

/-- Witness: `P = D = C = 1`, `dD = 1/2` needs compensating power `2`, and `2` restores the
capacity `1`. -/
example : (1 : ℝ) * 1 / (1 - 1/2) = 2 ∧ cap 2 (1 - 1/2) 1 = cap 1 1 1 := by
  norm_num [cap]

/-- The same witness with denominators cleared, checked by `decide` over `ℤ`: measuring `D`
and `dD` in halves (`D = 2`, `dD = 1`), the compensating power `P' = 2` is the unique integer in
`[0, 10]` with `P'·(D − dD) = P·D`. -/
example : (2 : ℤ) * (2 - 1) = 1 * 2 ∧
    ∀ P' : Fin 11, ((P' : ℕ) : ℤ) * (2 - 1) = 1 * 2 → (P' : ℕ) = 2 := by
  decide

/-- Ceiling `Pmax = 2`: the condition holds with equality, `1/2 ≤ 1 · (1 − 1/2)`. -/
example : (1/2 : ℝ) ≤ 1 * (1 - 1 / 2) ∧ (1/2 : ℝ) = 1 * (1 - 1 / 2) := by
  norm_num

/-- Ceiling `Pmax = 3/2`: the condition fails, `1/2 > 1 · (1 − 2/3) = 1/3`, matching the fact
that the required power `2` exceeds `3/2`. -/
example : ¬ ((1/2 : ℝ) ≤ 1 * (1 - 1 / (3/2))) ∧ (3/2 : ℝ) < 2 := by
  norm_num

/-- Both ceiling checks in the cleared form `P·D ≤ Pmax·(D − dD)` (equivalent to the ceiling
condition when `Pmax > 0` and `dD < D`), checked by `decide` over `ℤ`. With `D = 2, dD = 1`
(halves): `Pmax = 2, P = 1` gives `2 ≤ 2` (equality); scaling powers by `2`, `Pmax = 3/2, P = 1`
becomes `Pmax = 3, P = 2` and gives `4 ≤ 3`, which fails. -/
example : ((1 : ℤ) * 2 ≤ 2 * (2 - 1) ∧ (1 : ℤ) * 2 = 2 * (2 - 1)) ∧
    ¬ ((2 : ℤ) * 2 ≤ 3 * (2 - 1)) := by
  decide

/-- Complete loss: at `D = 0` the capacity is `0` whatever the power. -/
example : cap 1000 0 1 = 0 ∧ cap 1000 0 1 < cap 1 1 1 := by
  norm_num [cap]

/-- Negative control for part 2 without `P ≤ Pmax`: with `Pmax = -1`, `P = D = C = 1`,
`dD = 1/2`, the right side `1/2 ≤ 1·(1 − 1/(−1)) = 2` holds, but no `P' ≤ −1` restores the
capacity (it would need `P'·(1/2) = 1`). -/
example : (1/2 : ℝ) ≤ 1 * (1 - 1 / (-1)) ∧
    ¬ (∃ P' : ℝ, P' ≤ -1 ∧ cap P' (1 - 1/2) 1 = cap 1 1 1) := by
  refine ⟨by norm_num, ?_⟩
  rintro ⟨P', hP', h⟩
  simp only [cap] at h
  linarith

/-- Negative control for part 2 without `dD < D`: with `P = D = C = Pmax = 1` and `dD = 2`,
the negative power `P' = −1` satisfies `P' ≤ Pmax` and `cap (−1) (1 − 2) 1 = cap 1 1 1`, but
the right side `2 ≤ 1·(1 − 1/1) = 0` fails. -/
example : ((-1 : ℝ) ≤ 1 ∧ cap (-1) (1 - 2) 1 = cap 1 1 1) ∧ ¬ ((2 : ℝ) ≤ 1 * (1 - 1 / 1)) := by
  norm_num [cap]

end ViridisStatements.P5.CompensationUnderCeiling


namespace ViridisStatements.P5.CompensationUnderCeiling.Proof

open ViridisStatements.P5.CompensationUnderCeiling

/-- Interior: the power `P·D/(D − dD)` restores the capacity, and it is the only one. -/
theorem interior (P D dD C : ℝ) (hC : 0 < C) (hP : 0 < P) (hdD : 0 < dD) (hlt : dD < D) :
    cap (P * D / (D - dD)) (D - dD) C = cap P D C ∧
    ∀ P' : ℝ, cap P' (D - dD) C = cap P D C → P' = P * D / (D - dD) := by
  have hpos : 0 < D - dD := by linarith
  refine ⟨?_, ?_⟩
  · unfold cap
    rw [div_mul_cancel₀ _ hpos.ne']
  · intro P' h
    unfold cap at h
    rw [div_left_inj' hC.ne'] at h
    rw [eq_div_iff hpos.ne', h]

/-- Ceiling: compensation within `Pmax` is possible iff `dD ≤ D·(1 − P/Pmax)`. -/
theorem ceiling (P D dD C Pmax : ℝ) (hC : 0 < C) (hP : 0 < P) (hdD : 0 < dD) (hlt : dD < D)
    (hPmax : P ≤ Pmax) :
    (∃ P' : ℝ, P' ≤ Pmax ∧ cap P' (D - dD) C = cap P D C) ↔ dD ≤ D * (1 - P / Pmax) := by
  have hpos : 0 < D - dD := by linarith
  have hM : 0 < Pmax := lt_of_lt_of_le hP hPmax
  -- `dD ≤ D·(1 − P/Pmax)` is equivalent to `P·D ≤ Pmax·(D − dD)`.
  have key : dD ≤ D * (1 - P / Pmax) ↔ P * D ≤ Pmax * (D - dD) := by
    have : D * (1 - P / Pmax) = (Pmax * D - P * D) / Pmax := by
      field_simp
    rw [this, le_div_iff₀ hM]
    constructor <;> intro h <;> nlinarith
  rw [key]
  constructor
  · rintro ⟨P', hP', h⟩
    obtain ⟨-, huniq⟩ := interior P D dD C hC hP hdD hlt
    have he := huniq P' h
    rw [he, div_le_iff₀ hpos] at hP'
    exact hP'
  · intro h
    refine ⟨P * D / (D - dD), ?_, (interior P D dD C hC hP hdD hlt).1⟩
    rw [div_le_iff₀ hpos]
    exact h

/-- Divergence: the compensating power exceeds any bound as `dD → D⁻`. -/
theorem divergence (P D C : ℝ) (_hC : 0 < C) (hP : 0 < P) (hD : 0 < D) (M : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ dD : ℝ, D - δ < dD → dD < D → M < P * D / (D - dD) := by
  have hPD : 0 < P * D := mul_pos hP hD
  have hA : 0 < |M| + 1 := by positivity
  refine ⟨P * D / (|M| + 1), div_pos hPD hA, ?_⟩
  intro dD h1 h2
  have hpos : 0 < D - dD := by linarith
  have hsmall : D - dD < P * D / (|M| + 1) := by linarith
  rw [lt_div_iff₀ hA] at hsmall
  rw [lt_div_iff₀ hpos]
  have hM : M ≤ |M| := le_abs_self M
  nlinarith [abs_nonneg M]

/-- Complete loss: at `D = 0` every power gives capacity `0 < cap P D C`. -/
theorem complete_loss (P D C : ℝ) (hC : 0 < C) (hP : 0 < P) (hD : 0 < D) (P' : ℝ) :
    cap P' 0 C = 0 ∧ cap P' 0 C < cap P D C := by
  have h0 : cap P' 0 C = 0 := by simp [cap]
  refine ⟨h0, ?_⟩
  rw [h0]
  unfold cap
  positivity

theorem main : ViridisStatements.P5.CompensationUnderCeiling.Statement :=
  ⟨fun P D dD C hC hP hdD hlt => interior P D dD C hC hP hdD hlt,
   fun P D dD C Pmax hC hP hdD hlt hPmax => ceiling P D dD C Pmax hC hP hdD hlt hPmax,
   fun P D C hC hP hD M => divergence P D C hC hP hD M,
   fun P D C hC hP hD P' => complete_loss P D C hC hP hD P'⟩

end ViridisStatements.P5.CompensationUnderCeiling.Proof
