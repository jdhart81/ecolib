import Mathlib

/-!
# A route is no stronger than its weakest link, and alternatives never hurt: serial and parallel route reliability with a Lean proof

`EcoLib.Foundations.P6SerialParallel` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-research` at commit `751e8baf596e`
- `lean/ViridisStatements/P6/SerialParallel.lean` (SHA-256 `a882c97873aba9a8…`)
- `runs/2026-11-26_P6/proofs/P6.SerialParallel.lean` (SHA-256 `c128f57f223e46b9…`)
Certification: ENGINE_V3_VERIFY, evidence `runs/2026-11-26_P6/certification.json`
Engine run: 2026-11-26_P6
Public since: 2026-11-26

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

/-!
# P6 · Serial and parallel route reliability

Model: a route is a chain of corridor links indexed by a finite set `s`; link `i` is crossed with
probability `p i ∈ [0, 1]`. The serial success probability of the route is the product
`serial s p = ∏ i ∈ s, p i`. Given alternative routes indexed by `s` with success probabilities
`q i ∈ [0, 1]`, the expression `parallel s q = 1 - ∏ i ∈ s, (1 - q i)` is the probability that at
least one succeeds *if the routes fail independently*. Independence is a field assumption and is
not part of the mathematics below: `parallel` is just a real-valued formula.

`Statement`:
1. serial: if every `p i ∈ [0, 1]` for `i ∈ s`, then `serial s p ≤ p j` for every `j ∈ s`
   (a route is no stronger than its weakest link);
2. parallel: if every `q i ∈ [0, 1]` for `i ∈ s`, then `q j ≤ parallel s q ≤ 1` for every `j ∈ s`
   (alternatives are never worse than the best single route);
3. two routes, equality: for `p, q ∈ [0, 1]`,
   `1 - (1 - p) * (1 - q) = max p q ↔ (min p q = 0 ∨ max p q = 1)`.

Part 1 is the same inequality as part 3 of `P3.CascadedRecovery` with `p i = 1 - r i`; it is
restated here self-contained. No claim is made about any real link probability.
-/

namespace ViridisStatements.P6.SerialParallel

/-- Success probability of a route whose links have crossing probabilities `p`. -/
def serial {ι : Type} (s : Finset ι) (p : ι → ℝ) : ℝ := ∏ i ∈ s, p i

/-- Probability that at least one of the routes `s` succeeds, under independence. -/
def parallel {ι : Type} (s : Finset ι) (q : ι → ℝ) : ℝ := 1 - ∏ i ∈ s, (1 - q i)

/-- **Proposed sealed target `P6.SerialParallel`.** -/
def Statement : Prop :=
  (∀ (ι : Type) (s : Finset ι) (p : ι → ℝ), (∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) →
      ∀ j ∈ s, serial s p ≤ p j) ∧
  (∀ (ι : Type) (s : Finset ι) (q : ι → ℝ), (∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1) →
      ∀ j ∈ s, q j ≤ parallel s q ∧ parallel s q ≤ 1) ∧
  (∀ p q : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
      (1 - (1 - p) * (1 - q) = max p q ↔ (min p q = 0 ∨ max p q = 1)))

/-! ## Sanity checks -/

/-- Two links of `1/2` in series: the route succeeds with probability `1/4 < 1/2`. -/
example : serial Finset.univ ![(1/2 : ℝ), 1/2] = 1/4 ∧
    serial Finset.univ ![(1/2 : ℝ), 1/2] < 1/2 := by
  norm_num [serial, Fin.prod_univ_two]

/-- Two independent routes of `1/2` in parallel: at least one succeeds with probability
`3/4 > 1/2`, strictly above the best route. -/
example : parallel Finset.univ ![(1/2 : ℝ), 1/2] = 3/4 ∧
    1/2 < parallel Finset.univ ![(1/2 : ℝ), 1/2] := by
  norm_num [parallel, Fin.prod_univ_two]

/-- Part 3 at `p = q = 1/2`: the left side is `3/4`, not `max p q = 1/2`, and indeed neither
`min p q = 0` nor `max p q = 1`. -/
example : 1 - (1 - (1/2 : ℝ)) * (1 - 1/2) ≠ max (1/2 : ℝ) (1/2) ∧
    ¬ (min (1/2 : ℝ) (1/2) = 0 ∨ max (1/2 : ℝ) (1/2) = 1) := by
  norm_num

/-- Part 3 equality cases: a dead alternative (`q = 0`) or a sure route (`p = 1`). -/
example : 1 - (1 - (1/2 : ℝ)) * (1 - 0) = max (1/2 : ℝ) 0 ∧
    1 - (1 - (1 : ℝ)) * (1 - 1/2) = max (1 : ℝ) (1/2) := by
  norm_num

/-- Negative control for part 1: with an out-of-range "probability" `2`, links `2` and `1/2`
have product `1 > 1/2`, so the bound `p i ≤ 1` cannot be dropped. -/
example : 1/2 < serial Finset.univ ![(2 : ℝ), 1/2] := by
  norm_num [serial, Fin.prod_univ_two]

end ViridisStatements.P6.SerialParallel


namespace ViridisStatements.P6.SerialParallel.Proof

open ViridisStatements.P6.SerialParallel

/-- A product of factors in `[0, 1]` is at most any one of its factors. -/
theorem prod_le_factor {ι : Type} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (j : ι) (hj : j ∈ s) :
    ∏ i ∈ s, p i ≤ p j := by
  classical
  rw [← Finset.mul_prod_erase s p hj]
  have h0 : 0 ≤ p j := (hp j hj).1
  have h1 : ∏ i ∈ s.erase j, p i ≤ 1 :=
    Finset.prod_le_one (fun i hi => (hp i (Finset.mem_of_mem_erase hi)).1)
      (fun i hi => (hp i (Finset.mem_of_mem_erase hi)).2)
  calc p j * ∏ i ∈ s.erase j, p i ≤ p j * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ = p j := mul_one _

theorem serial_le {ι : Type} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) (j : ι) (hj : j ∈ s) : serial s p ≤ p j :=
  prod_le_factor s p hp j hj

theorem parallel_bounds {ι : Type} (s : Finset ι) (q : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1) (j : ι) (hj : j ∈ s) :
    q j ≤ parallel s q ∧ parallel s q ≤ 1 := by
  have hq' : ∀ i ∈ s, 0 ≤ 1 - q i ∧ 1 - q i ≤ 1 := fun i hi => by
    obtain ⟨a, b⟩ := hq i hi; constructor <;> linarith
  have hle := prod_le_factor s (fun i => 1 - q i) hq' j hj
  have hnn : 0 ≤ ∏ i ∈ s, (1 - q i) := Finset.prod_nonneg (fun i hi => (hq' i hi).1)
  unfold parallel
  constructor <;> simp only at hle <;> linarith

theorem two_routes (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    1 - (1 - p) * (1 - q) = max p q ↔ (min p q = 0 ∨ max p q = 1) := by
  rcases le_total p q with h | h
  · rw [max_eq_right h, min_eq_left h]
    constructor
    · intro e
      have : p * (1 - q) = 0 := by linarith
      rcases mul_eq_zero.mp this with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (by linarith)
    · rintro (e | e) <;> subst e <;> ring
  · rw [max_eq_left h, min_eq_right h]
    constructor
    · intro e
      have : q * (1 - p) = 0 := by linarith
      rcases mul_eq_zero.mp this with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (by linarith)
    · rintro (e | e) <;> subst e <;> ring

theorem main : ViridisStatements.P6.SerialParallel.Statement :=
  ⟨fun ι s p hp j hj => serial_le s p hp j hj,
   fun ι s q hq j hj => parallel_bounds s q hq j hj,
   fun p q hp0 hp1 hq0 hq1 => two_routes p q hp0 hp1 hq0 hq1⟩

end ViridisStatements.P6.SerialParallel.Proof
