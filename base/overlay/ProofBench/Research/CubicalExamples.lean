import ProofBench.Research.CubicalDiagrams

/-! Two further instantiations of the cubical separation library. -/

namespace CubicalDiagrams

open Finset

/-- The cube on an empty coordinate set has one corner and no cut edges. -/
theorem cutValue_of_isEmpty {I : Type*} [Fintype I] [DecidableEq I] [IsEmpty I]
    (w : Face I → ℕ) (A : Finset (Corner I)) : cutValue w A = 0 := by
  have h : crossingFaces A = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro f hf
    obtain ⟨⟨p, hp, _⟩, q, hq, _⟩ := (mem_crossingFaces_iff A f).mp hf
    have he : p = q := funext fun i => isEmptyElim i
    exact (mem_sdiff.mp hq).2 (he ▸ hp)
  simp [cutValue, h]

namespace Square

/-- The constant corner with both bits equal to the specified value. -/
def diagonalCorner (b : Bool) : Corner (Fin 2) := fun _ => b

private theorem count_faces : ∀ f : Face (Fin 2),
    (if f ∈ crossingFaces {diagonalCorner false} then 1 else 0) +
      (if f ∈ crossingFaces {diagonalCorner true} then 1 else 0) =
    (if f ∈ crossingFaces (coordinateSide 0 false) then 1 else 0) +
      (if f ∈ crossingFaces (coordinateSide 1 false) then 1 else 0) := by decide

/-- On the square, summing the two opposite singleton cuts counts every face
with the same multiplicity as summing the two coordinate cuts. -/
theorem opposite_cut_sum (w : Face (Fin 2) → ℕ) :
    cutValue w {diagonalCorner false} + cutValue w {diagonalCorner true} =
      cutValue w (coordinateSide 0 false) + cutValue w (coordinateSide 1 false) := by
  simp only [cutValue_eq_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro f _
  have scaled := congrArg (fun n : ℕ => n * w f) (count_faces f)
  simpa only [Nat.add_mul, ite_mul, one_mul, zero_mul] using scaled

variable {X : Type*} [Fintype X] [DecidableEq X] {G : SimpleGraph X}

/-- The opposite-corner separators are the usual intersection/union corners
of a pair of separations, with orientations determined by the chosen bit. -/
theorem corner_sides (D : Fin 2 → G.Separation) (b : Bool) :
    (lift D {diagonalCorner b}).A = side (D 0) b ∩ side (D 1) b ∧
    (lift D {diagonalCorner b}).B = side (D 0) (!b) ∪ side (D 1) (!b) := by
  constructor
  · ext x
    change x ∈ aggregate D {diagonalCorner b} ↔ _
    simp only [mem_aggregate_iff, mem_singleton, exists_eq_left, mem_inter, diagonalCorner]
    exact Fin.forall_fin_two
  · ext x
    change x ∈ aggregate D (univ \ {diagonalCorner b}) ↔ _
    simp only [mem_aggregate_complement_singleton, diagonalCorner, mem_union]
    rw [Fin.exists_fin_succ, Fin.exists_fin_one]
    rfl

/-- At the two opposite corners, the two induced separator orders sum to the
sum of the input orders for every pair of finite graph separations. -/
theorem opposite_order_sum (D : Fin 2 → G.Separation) :
    (lift D {diagonalCorner false}).order + (lift D {diagonalCorner true}).order =
      (D 0).order + (D 1).order := by
  rw [order_lift, order_lift, opposite_cut_sum, coordinate_order, coordinate_order]

/-- The cardinality formula of Bourneuf et al., Lemma 4.8, with the
two intersection/union separators written in their original orientation. -/
theorem opposite_corner_card_eq (D : Fin 2 → G.Separation) :
    (((D 0).A ∩ (D 1).A) ∩ ((D 0).B ∪ (D 1).B)).card +
      (((D 0).A ∪ (D 1).A) ∩ ((D 0).B ∩ (D 1).B)).card =
      (D 0).order + (D 1).order := by
  have orderAt (b : Bool) : (lift D {diagonalCorner b}).order =
      ((side (D 0) b ∩ side (D 1) b) ∩ (side (D 0) (!b) ∪ side (D 1) (!b))).card := by
    change ((lift D {diagonalCorner b}).A ∩ (lift D {diagonalCorner b}).B).card = _
    rw [(corner_sides D b).1, (corner_sides D b).2]
  have h := opposite_order_sum D
  rw [orderAt false, orderAt true] at h
  simpa [side, inter_comm] using h

end Square

end CubicalDiagrams
