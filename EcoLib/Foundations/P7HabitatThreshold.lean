import Mathlib

/-!
# The Levins extinction threshold under habitat loss: a Lean proof of the sign of the growth term

`EcoLib.Foundations.P7HabitatThreshold` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-research` at commit `fc7145b23e3d`
- `lean/ViridisStatements/P7/HabitatThreshold.lean` (SHA-256 `378845bc63602cb8…`)
- `runs/2026-11-28_P7/proofs/P7.HabitatThreshold.lean` (SHA-256 `f58d3802d99da8c7…`)
Certification: ENGINE_V3_VERIFY, evidence `runs/2026-11-28_P7/certification.json`
Engine run: 2026-11-28_P7
Public since: 2026-11-28

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

/-!
# P7 · The Levins extinction threshold under habitat loss

Model (Levins 1969, with habitat loss as in Lande 1987 and Nee and May 1992): the fraction `p`
of patches occupied changes at rate `dp/dt = growth c e h p = c·p·(h − p) − e·p`, where `c` is the
colonisation rate, `e` the extinction rate and `h` the fraction of patches still suitable. The
nontrivial equilibrium is `pstar c e h = h − e/c`.

`Statement` is about the **sign of the growth term** only. It says nothing about solutions of the
differential equation, and nothing about whether a real species follows this model or about any
value of `c`, `e` or `h`; those are field inputs. Each part holds for all real `c, e, h` with
`0 < c` and `0 < e`:

1. factorisation: `growth c e h p = c·p·(pstar c e h − p)` for every `p`;
2. below the threshold (`h ≤ e/c`): `growth c e h p < 0` for every `p > 0`;
3. above the threshold (`e/c < h`): `0 < pstar < h`, `growth` vanishes at `pstar`, is positive on
   `(0, pstar)` and negative above `pstar`;
4. Levins rule: `e/c < h ↔ 1 − h < 1 − e/c` (the destroyed fraction `1 − h` must stay below the
   intact-habitat occupancy `1 − e/c`);
5. the threshold `e/c` falls strictly when `c` rises and rises strictly when `e` rises.
-/

namespace ViridisStatements.P7.HabitatThreshold

/-- Levins growth term with habitat loss: `c·p·(h − p) − e·p`. -/
def growth (c e h p : ℝ) : ℝ := c * p * (h - p) - e * p

/-- Nontrivial equilibrium occupancy `p* = h − e/c`. -/
noncomputable def pstar (c e h : ℝ) : ℝ := h - e / c

/-- **Proposed sealed target `P7.HabitatThreshold`.** -/
def Statement : Prop :=
  (∀ c e h : ℝ, 0 < c → 0 < e →
      ∀ p : ℝ, growth c e h p = c * p * (pstar c e h - p)) ∧
  (∀ c e h : ℝ, 0 < c → 0 < e → h ≤ e / c →
      ∀ p : ℝ, 0 < p → growth c e h p < 0) ∧
  (∀ c e h : ℝ, 0 < c → 0 < e → e / c < h →
      0 < pstar c e h ∧ pstar c e h < h ∧ growth c e h (pstar c e h) = 0 ∧
      (∀ p : ℝ, 0 < p → p < pstar c e h → 0 < growth c e h p) ∧
      (∀ p : ℝ, pstar c e h < p → growth c e h p < 0)) ∧
  (∀ c e h : ℝ, 0 < c → 0 < e → (e / c < h ↔ 1 - h < 1 - e / c)) ∧
  (∀ c e : ℝ, 0 < c → 0 < e →
      (∀ c' : ℝ, c < c' → e / c' < e / c) ∧ (∀ e' : ℝ, e < e' → e / c < e' / c))

/-! ## Sanity checks -/

/-- Witness: `c = 2, e = 1, h = 1` gives `p* = 1/2`, and the growth at `p = 1/4` is `1/8 > 0`. -/
example : pstar 2 1 1 = 1/2 ∧ growth 2 1 1 (1/4) = 1/8 ∧ 0 < growth 2 1 1 (1/4) := by
  norm_num [pstar, growth]

/-- Witness: with habitat cut to `h = 1/2 = e/c` the growth at `p = 1/4` is `−1/8 < 0`. -/
example : growth 2 1 (1/2) (1/4) = -1/8 ∧ growth 2 1 (1/2) (1/4) < 0 := by
  norm_num [growth]

/-- Factorisation at the witness point: `c·p·(p* − p) = 2·(1/4)·(1/2 − 1/4) = 1/8`. -/
example : (2 : ℝ) * (1/4) * (pstar 2 1 1 - 1/4) = growth 2 1 1 (1/4) := by
  norm_num [pstar, growth]

/-- Negative control for part 2: without `0 < p` the strict sign fails, since the growth term
is `0` at `p = 0` even below the threshold (`h = 1/2 ≤ e/c = 1/2`). -/
example : ¬ (growth 2 1 (1/2) 0 < 0) := by
  norm_num [growth]

/-- Negative control for part 5: with `e = 0` (excluded by `0 < e`) the threshold does not fall
when `c` rises: `0/3 = 0/2`. -/
example : ¬ ((0 : ℝ) / 3 < 0 / 2) := by
  norm_num

end ViridisStatements.P7.HabitatThreshold


namespace ViridisStatements.P7.HabitatThreshold.Proof

open ViridisStatements.P7.HabitatThreshold

/-- Part 1: the growth term factorises through the equilibrium `p* = h - e/c`. -/
theorem growth_factor (c e h : ℝ) (hc : 0 < c) (p : ℝ) :
    growth c e h p = c * p * (pstar c e h - p) := by
  unfold growth pstar
  field_simp
  ring

/-- Part 2: at or below the threshold the growth term is negative for every `p > 0`. -/
theorem below (c e h : ℝ) (hc : 0 < c) (hle : h ≤ e / c) (p : ℝ) (hp : 0 < p) :
    growth c e h p < 0 := by
  rw [growth_factor c e h hc p]
  have hcp : 0 < c * p := mul_pos hc hp
  have hneg : pstar c e h - p < 0 := by unfold pstar; linarith
  exact mul_neg_of_pos_of_neg hcp hneg

/-- Part 3: above the threshold, `0 < p* < h`, `p*` is an equilibrium, and the growth term
points towards `p*` from both sides. -/
theorem above (c e h : ℝ) (hc : 0 < c) (he : 0 < e) (hlt : e / c < h) :
    0 < pstar c e h ∧ pstar c e h < h ∧ growth c e h (pstar c e h) = 0 ∧
      (∀ p : ℝ, 0 < p → p < pstar c e h → 0 < growth c e h p) ∧
      (∀ p : ℝ, pstar c e h < p → growth c e h p < 0) := by
  have hec : 0 < e / c := div_pos he hc
  have hps : 0 < pstar c e h := by unfold pstar; linarith
  refine ⟨hps, ?_, ?_, ?_, ?_⟩
  · unfold pstar; linarith
  · rw [growth_factor c e h hc]; ring
  · intro p hp hpp
    rw [growth_factor c e h hc p]
    exact mul_pos (mul_pos hc hp) (by linarith)
  · intro p hpp
    rw [growth_factor c e h hc p]
    exact mul_neg_of_pos_of_neg (mul_pos hc (by linarith)) (by linarith)

theorem main : ViridisStatements.P7.HabitatThreshold.Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c e h hc _ p
    exact growth_factor c e h hc p
  · intro c e h hc _ hle p hp
    exact below c e h hc hle p hp
  · intro c e h hc he hlt
    exact above c e h hc he hlt
  · intro c e h _ _
    constructor <;> intro H <;> linarith
  · intro c e hc he
    refine ⟨?_, ?_⟩
    · intro c' hc'
      exact div_lt_div_of_pos_left he hc hc'
    · intro e' he'
      exact div_lt_div_of_pos_right he' hc

end ViridisStatements.P7.HabitatThreshold.Proof
