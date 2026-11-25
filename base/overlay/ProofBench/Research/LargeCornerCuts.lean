import ProofBench.Research.CubicalDiagrams

/-! Large corner regions force large cuts in unbreakable graphs.
This specializes in dimension three to the finite graph case of Lemma 4.16
of Bourneuf, Carmesin, Kurkofka, and Planken. -/
namespace CubicalDiagrams

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {G : SimpleGraph X}

/-- Every separation of order at most t has some proper side with at most q vertices. -/
def Unbreakable (G : SimpleGraph X) (q t : ℕ) : Prop :=
  ∀ s : G.Separation, s.order ≤ t → (s.A \ s.B).card ≤ q ∨ (s.B \ s.A).card ≤ q

theorem order_ge_of_large_sides (q k : ℕ) (hG : Unbreakable G q (k - 1))
    (s : G.Separation) (hA : q + k ≤ s.A.card) (hB : q + k ≤ s.B.card) : k ≤ s.order := by
  by_contra! small
  have ord : s.order = (s.A ∩ s.B).card := rfl
  have a := card_sdiff_add_card_inter s.A s.B
  have b := card_sdiff_add_card_inter s.B s.A
  rw [inter_comm s.B s.A] at b
  rcases hG s (by omega) with h | h <;> omega

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Inclusive graph vertices belonging to the selected side in every coordinate. -/
def region (D : I → G.Separation) (p : Corner I) : Finset X :=
  aggregate D {p}

omit [DecidableEq I] in
theorem mem_region (D : I → G.Separation) (p : Corner I) (x : X) :
    x ∈ region D p ↔ ∀ i, x ∈ side (D i) (p i) := by
  simp [region, mem_aggregate_iff]

def largeCorners (D : I → G.Separation) (q k : ℕ) : Finset (Corner I) :=
  univ.filter fun p => q + k ≤ (region D p).card

private theorem region_subset (D : I → G.Separation) {A : Finset (Corner I)} {p : Corner I}
    (hp : p ∈ A) : region D p ⊆ aggregate D A := by
  intro x hx
  exact (mem_aggregate_iff _ _ _).mpr ⟨p, hp, (mem_region _ _ _).mp hx⟩

/-- Every cut separating two corners of inclusive size at least q + k has value at least k.
The diagram may have any finite number of oriented separations, of arbitrary orders. -/
theorem large_corner_cut (q k : ℕ) (hG : Unbreakable G q (k - 1))
    (D : I → G.Separation) (A : Finset (Corner I))
    (left : ∃ p ∈ largeCorners D q k, p ∈ A) (right : ∃ p ∈ largeCorners D q k, p ∉ A) :
    k ≤ cutValue (weight D) A := by
  obtain ⟨p, hlarge, hp⟩ := left
  obtain ⟨r, hrlarge, hr⟩ := right
  rw [← order_lift]
  apply order_ge_of_large_sides q k hG
  · exact (mem_filter.mp hlarge).2.trans (card_le_card (region_subset D hp))
  · exact (mem_filter.mp hrlarge).2.trans
      (card_le_card (region_subset D (mem_sdiff.mpr ⟨mem_univ r, hr⟩)))

end CubicalDiagrams
