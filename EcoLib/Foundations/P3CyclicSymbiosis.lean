import Mathlib

/-!
# Cyclic Industrial Symbiosis: A Lean Proof of the N-Partner Product Condition

`EcoLib.Foundations.P3CyclicSymbiosis` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-research` at commit `f539bad5adc4`
- `lean/ViridisStatements/P3/CyclicSymbiosis.lean` (SHA-256 `a6825700fb4c21d1…`)
- `runs/2026-11-18_P3/proofs/P3.CyclicSymbiosis.lean` (SHA-256 `1ca1065a18f21251…`)
Certification: ENGINE_V3_VERIFY, evidence `runs/2026-11-18_P3/certification.json`
Engine run: 2026-11-18_P3
Public since: 2026-11-18

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

/-!
# P3 · Cyclic industrial symbiosis: the N-partner product condition

Generalises the two-partner Reciprocity Corridor (canon Run-128,
`series/RC/PaperFormalization.lean`, copied as `context/ReciprocityCorridor.lean`) to a cycle
of `N ≥ 2` partners. Restated over Mathlib only.

Model: partners are indexed by `Fin N` and arranged in a cycle. Partner `i`
* ships a by-product flow `x i` to partner `i + 1` at cost `c i · x i` (`c i > 0`);
* receives the flow `x (i - 1)` of its predecessor, worth `v i · x (i - 1)` to it (`v i > 0`);
  indices are taken mod `N` (`prev i = (i + N - 1) mod N`).
Net benefit of partner `i`: `v i · x (prev i) - c i · x i` (linear, separable, one period, no
externalities; the Run-128 standing assumptions).

`Statement`: for `N ≥ 2` and positive `c, v`, there is a strictly positive flow `x` giving
every partner strictly positive net benefit **iff** `∏ c i < ∏ v i`.

For `N = 2` the cycle is the Run-128 bilateral exchange (`x 0 = x`, `x 1 = y`,
`v 0 = vX`, `c 0 = cX`, `v 1 = vY`, `c 1 = cY`), the net benefits are Run-128's `uX`, `uY`, and
`∏ c < ∏ v` is Run-128's `ProductCondition vX cX vY cY := cX * cY < vX * vY`; the sanity
checks below verify this agreement.

No claim is made about any real cost, value, partner or material.
-/

namespace ViridisStatements.P3.CyclicSymbiosis

/-- Predecessor on the cycle `Fin N`: `prev i = (i + N - 1) mod N`. -/
def prev {N : ℕ} (i : Fin N) : Fin N :=
  ⟨(i.val + (N - 1)) % N, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- Net benefit of partner `i`: value of the received flow minus cost of the shipped flow. -/
def net {N : ℕ} (c v x : Fin N → ℝ) (i : Fin N) : ℝ := v i * x (prev i) - c i * x i

/-- A strictly positive flow giving every partner strictly positive net benefit. -/
def StrictlyBeneficialFlow {N : ℕ} (c v x : Fin N → ℝ) : Prop :=
  (∀ i, 0 < x i) ∧ ∀ i, 0 < net c v x i

/-- The N-partner product condition `∏ c i < ∏ v i`. -/
def CycleProductCondition {N : ℕ} (c v : Fin N → ℝ) : Prop := ∏ i, c i < ∏ i, v i

/-- Run-128's two-partner product condition, copied verbatim (argument order `vX cX vY cY`). -/
def ProductCondition (vX cX vY cY : ℝ) : Prop := cX * cY < vX * vY

/-- **Proposed sealed target `P3.CyclicSymbiosis`.** -/
def Statement : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ c v : Fin N → ℝ, (∀ i, 0 < c i) → (∀ i, 0 < v i) →
    ((∃ x : Fin N → ℝ, StrictlyBeneficialFlow c v x) ↔ CycleProductCondition c v)

/-! ## Sanity checks -/

/-- The cycle structure on `Fin 3`: `0 ← 2`, `1 ← 0`, `2 ← 1`. -/
example : prev (0 : Fin 3) = 2 ∧ prev (1 : Fin 3) = 0 ∧ prev (2 : Fin 3) = 1 := by decide

/-- On `Fin 2` each partner's predecessor is the other partner. -/
example : prev (0 : Fin 2) = 1 ∧ prev (1 : Fin 2) = 0 := by decide

/-- `N = 2` agreement, condition: the cycle product condition is Run-128's
`ProductCondition vX cX vY cY`. -/
example (vX cX vY cY : ℝ) :
    CycleProductCondition ![cX, cY] ![vX, vY] ↔ ProductCondition vX cX vY cY := by
  simp [CycleProductCondition, ProductCondition, Fin.prod_univ_two]

/-- `N = 2` agreement, payoffs: partner `0` nets Run-128's `uX = vX*y - cX*x` and partner `1`
nets `uY = vY*x - cY*y` at the flow `![x, y]`. -/
example (vX cX vY cY x y : ℝ) :
    net ![cX, cY] ![vX, vY] ![x, y] 0 = vX * y - cX * x ∧
    net ![cX, cY] ![vX, vY] ![x, y] 1 = vY * x - cY * y := by
  have h0 : prev (0 : Fin 2) = 1 := by decide
  have h1 : prev (1 : Fin 2) = 0 := by decide
  simp [net, h0, h1]

/-- Three-partner witness: `c = (1,1,1)`, `v = (4, 1/2, 1)`, so `∏ c = 1 < 2 = ∏ v`. -/
example : CycleProductCondition ![(1 : ℝ), 1, 1] ![(4 : ℝ), 1/2, 1] := by
  simp only [CycleProductCondition, Fin.prod_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  norm_num

/-- The flow must be tuned: in the same economy the uniform flow `x = (1,1,1)` leaves
partner `1` with net benefit `1/2 - 1 < 0`, while the flow `x = (1, 9/20, 2/5)` benefits all
three partners (nets `3/5`, `1/20`, `1/20`). -/
example :
    net ![(1 : ℝ), 1, 1] ![(4 : ℝ), 1/2, 1] ![1, 1, 1] 1 < 0 ∧
    StrictlyBeneficialFlow ![(1 : ℝ), 1, 1] ![(4 : ℝ), 1/2, 1] ![1, 9/20, 2/5] := by
  have h0 : prev (0 : Fin 3) = 2 := by decide
  have h1 : prev (1 : Fin 3) = 0 := by decide
  have h2 : prev (2 : Fin 3) = 1 := by decide
  refine ⟨?_, ?_, ?_⟩
  · simp only [net, h1, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  · intro i; fin_cases i <;> simp
  · intro i
    fin_cases i
    · simp only [net, Fin.zero_eta, h0]; simp; norm_num
    · simp only [net, Fin.mk_one, h1]; simp; norm_num
    · simp only [net]
      rw [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl, h2]; simp; norm_num

/-- Negative control: `c = (2,2,2)`, `v = (1,1,1)` fails the product condition
(`8 < 1` is false), and the uniform flow indeed harms every partner. -/
example : ¬ CycleProductCondition ![(2 : ℝ), 2, 2] ![(1 : ℝ), 1, 1] ∧
    net ![(2 : ℝ), 2, 2] ![(1 : ℝ), 1, 1] ![1, 1, 1] 0 < 0 := by
  have h0 : prev (0 : Fin 3) = 2 := by decide
  constructor
  · simp only [CycleProductCondition, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    norm_num
  · simp only [net, h0]; simp

/-- Negative control: equality of products is not enough. With `c = v = (1,1)` the boundary
case `∏ c = ∏ v` fails the strict condition. -/
example : ¬ CycleProductCondition ![(1 : ℝ), 1] ![(1 : ℝ), 1] := by
  simp [CycleProductCondition, Fin.prod_univ_two]

end ViridisStatements.P3.CyclicSymbiosis


namespace ViridisStatements.P3.CyclicSymbiosis.Proof

open ViridisStatements.P3.CyclicSymbiosis

/-- Explicit form of the predecessor: `0 ↦ N - 1`, `i ↦ i - 1` otherwise. -/
lemma prev_val {N : ℕ} (i : Fin N) :
    (prev i).val = if i.val = 0 then N - 1 else i.val - 1 := by
  have hN := i.isLt
  unfold prev
  split_ifs with h
  · simp only [h, zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  · have : i.val + (N - 1) = (i.val - 1) + N := by omega
    simp only [this, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

/-- The predecessor map is injective, hence a bijection of the finite cycle. -/
lemma prev_bijective {N : ℕ} : Function.Bijective (prev : Fin N → Fin N) := by
  rw [← Finite.injective_iff_bijective]
  intro a b hab
  have ha := prev_val a
  have hb := prev_val b
  have := congrArg Fin.val hab
  have := a.isLt
  have := b.isLt
  ext
  split_ifs at ha hb <;> omega

/-- Reindexing along the cycle: `∏ x (prev i) = ∏ x i`. -/
lemma prod_prev {N : ℕ} (x : Fin N → ℝ) : ∏ i, x (prev i) = ∏ i, x i :=
  Fintype.prod_bijective prev prev_bijective _ _ (fun _ => rfl)

/-- Necessity: a strictly beneficial flow forces `∏ c < ∏ v`. -/
lemma necessity (N : ℕ) (hN : 2 ≤ N) (c v : Fin N → ℝ) (hc : ∀ i, 0 < c i)
    (x : Fin N → ℝ) (hx : StrictlyBeneficialFlow c v x) : CycleProductCondition c v := by
  obtain ⟨hxpos, hnet⟩ := hx
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hlt : ∏ i, (c i * x i) < ∏ i, (v i * x (prev i)) := by
    apply Finset.prod_lt_prod_of_nonempty _ _ hne
    · intro i _; exact mul_pos (hc i) (hxpos i)
    · intro i _
      have := hnet i
      unfold net at this
      linarith
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, prod_prev] at hlt
  have hX : 0 < ∏ i, x i := Finset.prod_pos (fun i _ => hxpos i)
  exact lt_of_mul_lt_mul_right hlt hX.le

/-- Sufficiency: under `∏ c < ∏ v` an explicit flow benefits every partner. -/
lemma sufficiency (N : ℕ) (hN : 2 ≤ N) (c v : Fin N → ℝ) (hc : ∀ i, 0 < c i)
    (hv : ∀ i, 0 < v i) (hP : CycleProductCondition c v) :
    ∃ x : Fin N → ℝ, StrictlyBeneficialFlow c v x := by
  unfold CycleProductCondition at hP
  have hCpos : 0 < ∏ i, c i := Finset.prod_pos (fun i _ => hc i)
  have hVpos : 0 < ∏ i, v i := Finset.prod_pos (fun i _ => hv i)
  set P : ℝ := (∏ i, v i) / (∏ i, c i) with hPdef
  have hP1 : 1 < P := by rw [hPdef, one_lt_div hCpos]; exact hP
  set s : ℝ := P ^ ((N : ℝ)⁻¹) with hsdef
  have hs1 : 1 < s := Real.one_lt_rpow hP1 (by positivity)
  have hs0 : 0 < s := by linarith
  have hsN : s ^ N = P := Real.rpow_inv_natCast_pow (by linarith) (by omega)
  -- per-partner ratios, with product one
  set a : Fin N → ℝ := fun i => v i / (c i * s) with hadef
  have hapos : ∀ i, 0 < a i := fun i => div_pos (hv i) (mul_pos (hc i) hs0)
  have haprod : ∏ i, a i = 1 := by
    simp only [hadef, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, hsN, hPdef]
    field_simp
  -- extend to ℕ and take prefix products
  set a' : ℕ → ℝ := fun j => if h : j < N then a ⟨j, h⟩ else 1 with ha'def
  have ha'pos : ∀ j, 0 < a' j := by
    intro j; simp only [ha'def]; split_ifs
    · exact hapos _
    · exact one_pos
  set y : ℕ → ℝ := fun k => ∏ j ∈ Finset.range (k + 1), a' j with hydef
  have hypos : ∀ k, 0 < y k := fun k => Finset.prod_pos (fun j _ => ha'pos j)
  set x : Fin N → ℝ := fun i => y i.val with hxdef
  -- the key recursion around the cycle
  have hrec : ∀ i, x i = a i * x (prev i) := by
    intro i
    have hpv := prev_val i
    have hi := i.isLt
    simp only [hxdef]
    split_ifs at hpv with h0
    · rw [hpv, h0]
      have hyN : y (N - 1) = 1 := by
        simp only [hydef]
        rw [show N - 1 + 1 = N by omega, ← haprod, ← Fin.prod_univ_eq_prod_range]
        apply Finset.prod_congr rfl
        intro j _
        simp [ha'def, j.isLt]
      rw [hyN, mul_one]
      simp only [hydef, zero_add, Finset.prod_range_one, ha'def]
      rw [dif_pos (by omega)]
      congr 1
      ext; simp [h0]
    · rw [hpv]
      simp only [hydef]
      rw [show i.val + 1 = (i.val - 1 + 1) + 1 by omega, Finset.prod_range_succ,
        show i.val - 1 + 1 = i.val by omega, mul_comm]
      congr 1
      simp only [ha'def, dif_pos hi]
  refine ⟨x, fun i => hypos _, fun i => ?_⟩
  unfold net
  rw [hrec i]
  have hX : 0 < x (prev i) := hypos _
  have hci := hc i
  have hvi := hv i
  have : c i * (a i * x (prev i)) = v i * x (prev i) / s := by
    simp only [hadef]; field_simp
  rw [this]
  have hvx : 0 < v i * x (prev i) := mul_pos hvi hX
  rw [sub_pos, div_lt_iff₀ hs0]
  nlinarith

theorem main : ViridisStatements.P3.CyclicSymbiosis.Statement := by
  intro N hN c v hc hv
  exact ⟨fun ⟨x, hx⟩ => necessity N hN c v hc x hx, sufficiency N hN c v hc hv⟩

/-- `N = 2` corollary: specialising `main` to the two-partner cycle gives Run-128's strict
feasibility test (Theorem 2): strictly positive flows `x, y` with both payoffs
`uX = vX*y - cX*x` and `uY = vY*x - cY*y` strictly positive exist iff
`ProductCondition vX cX vY cY`. -/
theorem two_partner_corridor (vX cX vY cY : ℝ) (hvX : 0 < vX) (hcX : 0 < cX)
    (hvY : 0 < vY) (hcY : 0 < cY) :
    (∃ x y : ℝ, 0 < x ∧ 0 < y ∧ 0 < vX * y - cX * x ∧ 0 < vY * x - cY * y) ↔
      ProductCondition vX cX vY cY := by
  have h0 : prev (0 : Fin 2) = 1 := by decide
  have h1 : prev (1 : Fin 2) = 0 := by decide
  have hc : ∀ i, 0 < (![cX, cY] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> simp [hcX, hcY]
  have hv : ∀ i, 0 < (![vX, vY] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> simp [hvX, hvY]
  have key := main 2 le_rfl ![cX, cY] ![vX, vY] hc hv
  have hcond : CycleProductCondition ![cX, cY] ![vX, vY] ↔ ProductCondition vX cX vY cY := by
    simp [CycleProductCondition, ProductCondition, Fin.prod_univ_two]
  rw [← hcond, ← key]
  constructor
  · rintro ⟨x, y, hx, hy, hX, hY⟩
    refine ⟨![x, y], ?_, ?_⟩
    · intro i; fin_cases i <;> simp [hx, hy]
    · intro i
      fin_cases i
      · simpa [net, h0] using hX
      · simpa [net, h1] using hY
  · rintro ⟨f, hpos, hnet⟩
    refine ⟨f 0, f 1, hpos 0, hpos 1, ?_, ?_⟩
    · simpa [net, h0] using hnet 0
    · simpa [net, h1] using hnet 1

end ViridisStatements.P3.CyclicSymbiosis.Proof
