import Mathlib

/-!
# One spare corridor is the least price of surviving any single corridor loss: a note for corridor planners with a Lean proof

`EcoLib.Corridors.P6SingleFailureRobust` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-research` at commit `c64a9fe926bf`
- `lean/ViridisStatements/P6/SingleFailureRobust.lean` (SHA-256 `f7c925574028357c…`)
- `runs/2026-11-25_P6/proofs/P6.SingleFailureRobust.lean` (SHA-256 `4ffe72496f957873…`)
Certification: ENGINE_V3_VERIFY, evidence `runs/2026-11-25_P6/certification.json`
Engine run: 2026-11-25_P6
Public since: 2026-11-25

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

/-!
# P6 · Single-failure robustness costs at least one spare corridor

Model: as in `P6.MinimalNetwork` (restated here, nothing is imported from it). Habitat patches are
the vertices of a finite type `V`, corridors are the edges of `G : SimpleGraph V`,
`n = Fintype.card V` and `m = G.edgeFinset.card`. Removing corridor `e` is `G.deleteEdges {e}`.

A network *survives any single corridor failure* if it is connected and stays connected after the
removal of any one of its corridors.

`Statement` (for every finite `V` with decidable equality and every `G` with decidable adjacency):
if `2 ≤ n` and `G` survives any single corridor failure, then `n ≤ m`.

So a robust network needs at least one corridor more than the `n - 1` of a tree. The triangle and
the 4-cycle attain the bound. For `n = 2` no simple graph satisfies the hypotheses, so the
statement holds there vacuously. This is classical graph theory, not a new theorem. No claim is
made about any real corridor, failure mode or landscape.
-/

namespace ViridisStatements.P6.SingleFailureRobust

/-- Number of habitat patches `n`. -/
def patchCount (V : Type) [Fintype V] : ℕ := Fintype.card V

/-- Number of corridors `m` of a corridor network `G`. -/
def corridorCount {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- `G` is connected and stays connected after the loss of any one corridor. -/
def SurvivesSingleFailure {V : Type} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).Connected

/-- **Proposed sealed target `P6.SingleFailureRobust`.** -/
def Statement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    2 ≤ patchCount V → SurvivesSingleFailure G → patchCount V ≤ corridorCount G

/-! ## Sanity checks -/

/-- Attainment witness 1: the triangle (complete graph on `Fin 3`) has `2 ≤ n`, survives any
single corridor failure, and has `m = 3 = n`. -/
example : 2 ≤ patchCount (Fin 3) ∧
    (⊤ : SimpleGraph (Fin 3)).Connected ∧
    (∀ e ∈ (⊤ : SimpleGraph (Fin 3)).edgeSet, ((⊤ : SimpleGraph (Fin 3)).deleteEdges {e}).Connected) ∧
    corridorCount (⊤ : SimpleGraph (Fin 3)) = 3 ∧
    corridorCount (⊤ : SimpleGraph (Fin 3)) = patchCount (Fin 3) := by
  decide

/-- The 4-cycle: corridors `0–1, 1–2, 2–3, 3–0`. -/
def cycle4 : SimpleGraph (Fin 4) where
  Adj i j := (i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val
  symm := fun _ _ h => h.symm
  loopless := ⟨fun i h => by omega⟩

instance : DecidableRel cycle4.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val))

/-- Attainment witness 2: the 4-cycle has `2 ≤ n`, survives any single corridor failure, and has
`m = 4 = n`. -/
example : 2 ≤ patchCount (Fin 4) ∧
    cycle4.Connected ∧
    (∀ e ∈ cycle4.edgeSet, (cycle4.deleteEdges {e}).Connected) ∧
    corridorCount cycle4 = 4 ∧
    corridorCount cycle4 = patchCount (Fin 4) := by
  decide

/-- Negative control: on a single patch the hypotheses other than `2 ≤ n` hold (the empty network
is connected and has no corridor to lose) yet `m = 0 < 1 = n`; so `2 ≤ n` cannot be dropped. -/
example : (⊥ : SimpleGraph (Fin 1)).Connected ∧
    (∀ e ∈ (⊥ : SimpleGraph (Fin 1)).edgeSet, ((⊥ : SimpleGraph (Fin 1)).deleteEdges {e}).Connected) ∧
    corridorCount (⊥ : SimpleGraph (Fin 1)) < patchCount (Fin 1) := by
  decide

/-- Check of the `n = 2` case: the single corridor `0–1` is connected but removing it
disconnects, so no simple graph on two patches satisfies the hypotheses. -/
example : (⊤ : SimpleGraph (Fin 2)).Connected ∧
    ¬ ((⊤ : SimpleGraph (Fin 2)).deleteEdges {s(0, 1)}).Connected ∧
    ¬ (⊥ : SimpleGraph (Fin 2)).Connected := by
  decide

end ViridisStatements.P6.SingleFailureRobust


namespace ViridisStatements.P6.SingleFailureRobust.Proof

open SimpleGraph ViridisStatements.P6.SingleFailureRobust

/-- The number of corridors as a `Nat.card` of the edge set. -/
lemma corridorCount_eq {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : corridorCount G = Nat.card G.edgeSet := by
  rw [corridorCount, Nat.card_eq_fintype_card, ← edgeFinset_card]

lemma patchCount_eq (V : Type) [Fintype V] : patchCount V = Nat.card V := by
  rw [patchCount, Nat.card_eq_fintype_card]

/-- In a tree, every corridor is a bridge, so deleting it disconnects the network. -/
lemma tree_delete_not_connected {V : Type} (G : SimpleGraph V) (hT : G.IsTree)
    (e : Sym2 V) (he : e ∈ G.edgeSet) : ¬ (G.deleteEdges {e}).Connected := by
  have hb : G.IsBridge e := isAcyclic_iff_forall_edge_isBridge.mp hT.IsAcyclic he
  induction e using Sym2.ind with
  | _ u v =>
    rw [isBridge_iff] at hb
    intro hc
    apply hb.2
    have := hc.preconnected u v
    simpa [deleteEdges] using this

/-- A connected graph on at least two vertices has an edge. -/
lemma exists_edge {V : Type} [Fintype V] (G : SimpleGraph V) (hc : G.Connected)
    (h2 : 2 ≤ Fintype.card V) : ∃ e, e ∈ G.edgeSet := by
  obtain ⟨u, v, huv⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
  obtain ⟨p⟩ := hc.preconnected u v
  cases p with
  | nil => exact absurd rfl huv
  | cons h _ => exact ⟨_, (G.mem_edgeSet).mpr h⟩

theorem main : ViridisStatements.P6.SingleFailureRobust.Statement := by
  intro V _ _ G _ h2 hS
  obtain ⟨hc, hdel⟩ := hS
  by_contra hlt
  push_neg at hlt
  have hle : patchCount V ≤ corridorCount G + 1 := by
    rw [patchCount_eq, corridorCount_eq]
    exact hc.card_vert_le_card_edgeSet_add_one
  have heq : Nat.card G.edgeSet + 1 = Nat.card V := by
    have h1 := corridorCount_eq G
    have h3 := patchCount_eq V
    omega
  have hT : G.IsTree := isTree_iff_connected_and_card.mpr ⟨hc, heq⟩
  obtain ⟨e, he⟩ := exists_edge G hc h2
  exact tree_delete_not_connected G hT e he (hdel e he)

/-- Attainment witness 1 (restated from the sealed module): the triangle. -/
theorem triangle_attains : 2 ≤ patchCount (Fin 3) ∧
    SurvivesSingleFailure (⊤ : SimpleGraph (Fin 3)) ∧
    corridorCount (⊤ : SimpleGraph (Fin 3)) = patchCount (Fin 3) := by
  unfold SurvivesSingleFailure
  decide

/-- Attainment witness 2 (restated from the sealed module): the 4-cycle. -/
theorem cycle4_attains : 2 ≤ patchCount (Fin 4) ∧
    SurvivesSingleFailure cycle4 ∧
    corridorCount cycle4 = patchCount (Fin 4) := by
  unfold SurvivesSingleFailure
  decide

end ViridisStatements.P6.SingleFailureRobust.Proof
