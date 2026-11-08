import Mathlib

/-!
# The 8-connected bit-quad Euler formula for finite rasters: a Lean proof by vertex double counting

`EcoLib.Foundations.P1BitQuad` in EcoLib, the Lean library of Viridis's machine-checked results.

Source: `jdhart81/viridis-research` at commit `d77d4365f206`
- `lean/ViridisStatements/P1/BitQuad.lean` (SHA-256 `cd3cdeba48f67f95…`)
- `runs/2026-10-28_P1/proofs/P1.BitQuad.lean` (SHA-256 `328a9a292c6c09ac…`)
Certification: ENGINE_V3_VERIFY, evidence `runs/2026-10-28_P1/certification.json`
Engine run: 2026-10-28_P1
Public since: 2026-10-28

Lean checks that each proof establishes its stated theorem from its stated hypotheses. It does not check that the hypotheses describe nature: none of these results is field-validated unless its module says so.
Empirical validation: none recorded (not field-validated).
-/

/-!
# P1 · L1: the bit-quad formula for an 8-connected raster

A raster is a finite set `B` of pixels in `ℤ × ℤ`. Pixel `(i, j)` stands for the
closed unit square `[i, i+1] × [j, j+1]`. `K B` is the union of the closed
squares of `B`. It is a cubical complex, and its vertices, edges and faces are
counted below. Two pixels that share only a corner meet in `K B`, which is the
8-connected reading of the foreground.

`Statement` says that for every finite raster,
`4 · χ(K B) = Q₁ − Q₃ − 2·Q_D`. Here `Q₁`, `Q₃` and `Q_D` count the 2×2 windows
that hold exactly one pixel of `B`, exactly three pixels of `B`, and exactly two
diagonally opposite pixels of `B` (Gray 1971).

This is the first rung (L1) of the P1 lemma ladder. See
`projects/P1/context/STATEMENT_PROPOSAL.md`.
-/

namespace ViridisStatements.P1.BitQuad

/-- A pixel, named by its lower-left lattice corner. -/
abbrev Pixel := ℤ × ℤ

/-- The four lattice corners of pixel `p`. -/
def corners (p : Pixel) : Finset (ℤ × ℤ) :=
  {(p.1, p.2), (p.1 + 1, p.2), (p.1, p.2 + 1), (p.1 + 1, p.2 + 1)}

/-- Vertices of `K B`: every corner of every pixel of `B`. -/
def vertices (B : Finset Pixel) : Finset (ℤ × ℤ) :=
  B.biUnion corners

/-- Horizontal unit edges `[(i, j), (i + 1, j)]` of `K B`, named by their left
end. These are the bottom edge `(i, j)` and the top edge `(i, j + 1)` of each
pixel `(i, j)` of `B`. -/
def hEdges (B : Finset Pixel) : Finset (ℤ × ℤ) :=
  B.biUnion fun p => {(p.1, p.2), (p.1, p.2 + 1)}

/-- Vertical unit edges `[(i, j), (i, j + 1)]` of `K B`, named by their lower
end. These are the left edge `(i, j)` and the right edge `(i + 1, j)` of each
pixel `(i, j)` of `B`. -/
def vEdges (B : Finset Pixel) : Finset (ℤ × ℤ) :=
  B.biUnion fun p => {(p.1, p.2), (p.1 + 1, p.2)}

/-- The Euler characteristic `V − E + F` of `K B`. -/
def euler (B : Finset Pixel) : ℤ :=
  ((vertices B).card : ℤ) - (((hEdges B).card : ℤ) + (vEdges B).card) + B.card

/-- The 2×2 window centred on the lattice point `v`, as four membership bits in
this order: lower-left, lower-right, upper-left, upper-right. -/
def bits (B : Finset Pixel) (v : ℤ × ℤ) : Bool × Bool × Bool × Bool :=
  (decide ((v.1 - 1, v.2 - 1) ∈ B), decide ((v.1, v.2 - 1) ∈ B),
   decide ((v.1 - 1, v.2) ∈ B), decide ((v.1, v.2) ∈ B))

/-- The number of pixels of `B` in the window centred on `v`. -/
def windowCount (B : Finset Pixel) (v : ℤ × ℤ) : ℕ :=
  match bits B v with
  | (a, b, c, d) => a.toNat + b.toNat + c.toNat + d.toNat

/-- True when the window centred on `v` holds exactly two diagonally opposite
pixels of `B`. -/
def isDiagonal (B : Finset Pixel) (v : ℤ × ℤ) : Bool :=
  match bits B v with
  | (a, b, c, d) => (a && d && !b && !c) || (b && c && !a && !d)

/-- Windows holding exactly one pixel of `B`. Every window that meets `B` is
centred on a vertex of `K B`, so counting over `vertices B` counts each such
window exactly once. -/
def Q1 (B : Finset Pixel) : ℕ :=
  ((vertices B).filter fun v => windowCount B v = 1).card

/-- Windows holding exactly three pixels of `B`. -/
def Q3 (B : Finset Pixel) : ℕ :=
  ((vertices B).filter fun v => windowCount B v = 3).card

/-- Windows holding exactly two diagonally opposite pixels of `B`. -/
def QD (B : Finset Pixel) : ℕ :=
  ((vertices B).filter fun v => isDiagonal B v = true).card

/-- **Sealed target `P1.BitQuad`.** For every finite raster `B`,
`4 · χ(K B) = Q₁ − Q₃ − 2·Q_D`. -/
def Statement : Prop :=
  ∀ B : Finset Pixel, 4 * euler B = (Q1 B : ℤ) - Q3 B - 2 * QD B

/-! ## Sanity checks

These checks are proved by computation inside the sealed module, so the
definitions above mean what their comments say. -/

/-- A single pixel: `V = 4`, `E = 4`, `F = 1`, so `χ = 1`, and its four windows
each hold one pixel. -/
example : euler {(0, 0)} = 1 ∧ Q1 {(0, 0)} = 4 ∧ Q3 {(0, 0)} = 0 ∧ QD {(0, 0)} = 0 := by
  decide

/-- Two pixels that touch only at a corner form one 8-connected piece: `χ = 1`,
and the shared corner is a diagonal window. -/
example : euler {(0, 0), (1, 1)} = 1 ∧ QD {(0, 0), (1, 1)} = 1 ∧ Q1 {(0, 0), (1, 1)} = 6 := by
  decide

/-- A 2×2 solid block is contractible: `χ = 1`. -/
example : euler {(0, 0), (1, 0), (0, 1), (1, 1)} = 1 := by
  decide

/-- The 3×3 ring (eight pixels around one hole) has `χ = 0`. -/
example : euler {(0, 0), (1, 0), (2, 0), (0, 1), (2, 1), (0, 2), (1, 2), (2, 2)} = 0 := by
  decide

end ViridisStatements.P1.BitQuad


namespace ViridisStatements.P1.BitQuad.Proof

open ViridisStatements.P1.BitQuad

/-- Membership in `vertices`. -/
theorem mem_vertices (B : Finset Pixel) (v : ℤ × ℤ) :
    v ∈ vertices B ↔ ∃ p ∈ B, v ∈ corners p := by
  unfold vertices
  simp only [Finset.mem_biUnion]

theorem mem_corners (p v : ℤ × ℤ) :
    v ∈ corners p ↔ v = (p.1, p.2) ∨ v = (p.1 + 1, p.2) ∨ v = (p.1, p.2 + 1) ∨
      v = (p.1 + 1, p.2 + 1) := by
  unfold corners
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- A horizontal edge is present iff the pixel above or below it is in `B`. -/
theorem mem_hEdges (B : Finset Pixel) (h : ℤ × ℤ) :
    h ∈ hEdges B ↔ (h.1, h.2) ∈ B ∨ (h.1, h.2 - 1) ∈ B := by
  unfold hEdges
  simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨p, hp, rfl | rfl⟩
    · left; simpa using hp
    · right; simpa using hp
  · rintro (h1 | h1)
    · exact ⟨_, h1, Or.inl rfl⟩
    · exact ⟨_, h1, Or.inr (by simp)⟩

/-- A vertical edge is present iff the pixel right or left of it is in `B`. -/
theorem mem_vEdges (B : Finset Pixel) (e : ℤ × ℤ) :
    e ∈ vEdges B ↔ (e.1, e.2) ∈ B ∨ (e.1 - 1, e.2) ∈ B := by
  unfold vEdges
  simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨p, hp, rfl | rfl⟩
    · left; simpa using hp
    · right; simpa using hp
  · rintro (h1 | h1)
    · exact ⟨_, h1, Or.inl rfl⟩
    · exact ⟨_, h1, Or.inr (by simp)⟩

/-- Shift-counting: if every translate `x + (a, b)` of `S` lies in `V`, then
counting the `v ∈ V` with `v - (a, b) ∈ S` gives `|S|`. -/
theorem card_shift (V S : Finset (ℤ × ℤ)) (a b : ℤ)
    (hS : ∀ x ∈ S, (x.1 + a, x.2 + b) ∈ V) :
    (V.filter fun v => (v.1 - a, v.2 - b) ∈ S).card = S.card := by
  apply Finset.card_bij (fun v _ => (v.1 - a, v.2 - b))
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro v₁ _ v₂ _ h
    simp only [Prod.mk.injEq] at h
    ext <;> omega
  · intro x hx
    refine ⟨(x.1 + a, x.2 + b), Finset.mem_filter.mpr ⟨hS x hx, ?_⟩, ?_⟩
    · simpa using hx
    · simp

theorem sum_shift (V S : Finset (ℤ × ℤ)) (a b : ℤ)
    (hS : ∀ x ∈ S, (x.1 + a, x.2 + b) ∈ V) :
    (∑ v ∈ V, if (v.1 - a, v.2 - b) ∈ S then (1 : ℤ) else 0) = S.card := by
  rw [Finset.sum_boole, card_shift V S a b hS]

theorem main : ViridisStatements.P1.BitQuad.Statement := by
  intro B
  set V := vertices B with hV
  -- inclusion facts
  have hB : ∀ x ∈ B, ∀ a b : ℤ, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
      (x.1 + a, x.2 + b) ∈ V := by
    intro x hx a b ha hb
    rw [hV, mem_vertices]
    refine ⟨x, hx, ?_⟩
    rw [mem_corners]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  have hH : ∀ x ∈ hEdges B, ∀ a : ℤ, (a = 0 ∨ a = 1) → (x.1 + a, x.2 + 0) ∈ V := by
    intro x hx a ha
    rw [mem_hEdges] at hx
    rcases hx with hx | hx
    · have := hB _ hx a 0 ha (Or.inl rfl)
      simpa using this
    · have := hB _ hx a 1 ha (Or.inr rfl)
      simpa using this
  have hVe : ∀ x ∈ vEdges B, ∀ b : ℤ, (b = 0 ∨ b = 1) → (x.1 + 0, x.2 + b) ∈ V := by
    intro x hx b hb
    rw [mem_vEdges] at hx
    rcases hx with hx | hx
    · have := hB _ hx 0 b (Or.inl rfl) hb
      simpa using this
    · have := hB _ hx 1 b (Or.inr rfl) hb
      simpa using this
  -- the four expressions as sums over V
  have eV : ((V.card : ℤ)) = ∑ v ∈ V, (1 : ℤ) := by simp
  have eF11 := sum_shift V B 1 1 (fun x hx => hB x hx 1 1 (Or.inr rfl) (Or.inr rfl))
  have eF01 := sum_shift V B 0 1 (fun x hx => hB x hx 0 1 (Or.inl rfl) (Or.inr rfl))
  have eF10 := sum_shift V B 1 0 (fun x hx => hB x hx 1 0 (Or.inr rfl) (Or.inl rfl))
  have eF00 := sum_shift V B 0 0 (fun x hx => hB x hx 0 0 (Or.inl rfl) (Or.inl rfl))
  have eH10 := sum_shift V (hEdges B) 1 0 (fun x hx => hH x hx 1 (Or.inr rfl))
  have eH00 := sum_shift V (hEdges B) 0 0 (fun x hx => hH x hx 0 (Or.inl rfl))
  have eV01 := sum_shift V (vEdges B) 0 1 (fun x hx => hVe x hx 1 (Or.inr rfl))
  have eV00 := sum_shift V (vEdges B) 0 0 (fun x hx => hVe x hx 0 (Or.inl rfl))
  have eQ1 : ((Q1 B : ℕ) : ℤ) = ∑ v ∈ V, if windowCount B v = 1 then (1 : ℤ) else 0 := by
    rw [Finset.sum_boole]; rfl
  have eQ3 : ((Q3 B : ℕ) : ℤ) = ∑ v ∈ V, if windowCount B v = 3 then (1 : ℤ) else 0 := by
    rw [Finset.sum_boole]; rfl
  have eQD : ((QD B : ℕ) : ℤ) = ∑ v ∈ V, if isDiagonal B v = true then (1 : ℤ) else 0 := by
    rw [Finset.sum_boole]; rfl
  have key : 4 * euler B = ∑ v ∈ V,
      ((4 : ℤ) - 2 * ((if (v.1 - 1, v.2 - 0) ∈ hEdges B then 1 else 0)
        + (if (v.1 - 0, v.2 - 0) ∈ hEdges B then 1 else 0)
        + (if (v.1 - 0, v.2 - 1) ∈ vEdges B then 1 else 0)
        + (if (v.1 - 0, v.2 - 0) ∈ vEdges B then 1 else 0))
        + ((if (v.1 - 1, v.2 - 1) ∈ B then 1 else 0)
        + (if (v.1 - 0, v.2 - 1) ∈ B then 1 else 0)
        + (if (v.1 - 1, v.2 - 0) ∈ B then 1 else 0)
        + (if (v.1 - 0, v.2 - 0) ∈ B then 1 else 0))) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [eF11, eF01, eF10, eF00, eH10, eH00, eV01, eV00]
    unfold euler
    rw [← hV]
    simp
    ring
  rw [key, eQ1, eQ3, eQD, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  obtain ⟨x, y⟩ := v
  have hne : (x - 1, y - 1) ∈ B ∨ (x, y - 1) ∈ B ∨ (x - 1, y) ∈ B ∨ (x, y) ∈ B := by
    rw [hV, mem_vertices] at hv
    obtain ⟨p, hp, hc⟩ := hv
    rw [mem_corners] at hc
    rcases hc with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
    · right; right; right; exact hp
    · right; right; left; simpa using hp
    · right; left; simpa using hp
    · left; simpa using hp
  unfold windowCount isDiagonal bits
  simp only [sub_zero, mem_hEdges, mem_vEdges]
  by_cases ha : (x - 1, y - 1) ∈ B <;> by_cases hb : (x, y - 1) ∈ B <;>
    by_cases hc : (x - 1, y) ∈ B <;> by_cases hd : (x, y) ∈ B <;>
    simp [ha, hb, hc, hd] at hne ⊢

end ViridisStatements.P1.BitQuad.Proof
