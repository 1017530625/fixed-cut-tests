import ProofBench.Research.CornerCrossing
import ProofBench.Research.CubicalP118

/-!
# Uniform crossing from a cubical flower

In Lemma 4.17 of Bourneuf, Carmesin, Kurkofka and Planken, the centre of a separator partition is
distinguished and its two links are unordered. On each separator the two
other coordinates agree up to a single Boolean permutation, independent
of the graph vertex. Only the zero-weight faces of a flower are needed.
-/

namespace CornerSection

open Finset CubicalDiagrams

private def relabel (swap b : Bool) : Bool := if swap then !b else b

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
/-- On an allowed face free in the first coordinate, the two remaining bits
are either both free or both fixed, with exactly one matching the pole. -/
private theorem allowed_face :
    ∀ (p : CornerLemma.Vertex) (f : CornerLemma.Face) (i j t : Fin 3),
    i ≠ j → i ≠ t → j ≠ t → f i = none → CornerLemma.dim f ≠ 2 →
    (CornerLemma.dim f = 1 →
      ¬(CornerLemma.InFace p f ∨ CornerLemma.InFace (fun a => !(p a)) f)) →
    f j = (f t).map (relabel (p j == p t)) := by decide

private theorem mapped_none (swap : Bool) (o : Option Bool) :
    o.map (relabel swap) = none ↔ o = none := by cases o <;> simp

private theorem mapped_bit :
    ∀ (swap b : Bool) (o : Option Bool),
      o.map (relabel swap) = some b ↔ o = some (relabel swap b) := by decide

variable {X : Type*} [Fintype X] [DecidableEq X] {G : SimpleGraph X}

private theorem separator_iff_free (D : Fin 3 → G.Separation) (x : X) (i : Fin 3) :
    x ∈ (D i).separator ↔ faceOf D x i = none := by
  change x ∈ side (D i) false ∩ side (D i) true ↔ _
  rw [mem_inter, ← agrees_iff D x i false, ← agrees_iff D x i true]
  cases h : faceOf D x i with
  | none => simp
  | some b => cases b <;> simp

private theorem proper_iff_bit (D : Fin 3 → G.Separation) (x : X) (i : Fin 3) (b : Bool) :
    x ∈ proper (D i) b ↔ faceOf D x i = some b := by
  rw [proper, mem_sdiff, ← agrees_iff D x i b, ← agrees_iff D x i (!b)]
  cases h : faceOf D x i with
  | none => simp
  | some a => cases a <;> cases b <;> simp

/-- A fixed bit permutation on all graph vertices in a separator identifies
the centres and identifies the two links as an unordered pair. -/
private theorem partition_of_relabel (D : Fin 3 → G.Separation) (i j t : Fin 3)
    (swap : Bool) (aligned : ∀ x ∈ (D i).separator,
      faceOf D x j = (faceOf D x t).map (relabel swap)) :
    partition (D i) (D j) = partition (D i) (D t) := by
  have centres : centre (D i) (D j) = centre (D i) (D t) := by
    ext x
    simp only [centre, mem_inter]
    apply and_congr_right
    intro hx
    rw [separator_iff_free D x j, separator_iff_free D x t, aligned x hx, mapped_none]
  have links (b : Bool) : link (D i) (D j) b = link (D i) (D t) (relabel swap b) := by
    ext x
    simp only [link, mem_inter]
    apply and_congr_right
    intro hx
    rw [proper_iff_bit D x j b, proper_iff_bit D x t (relabel swap b),
      aligned x hx, mapped_bit]
  unfold partition
  rw [centres, links false, links true]
  cases swap
  · rfl
  · exact congrArg (Prod.mk _) (Finset.pair_comm _ _)

/-- Lemma 4.17. For any three finite graph separations whose cubical
visualisation is a flower, each separator has a common tripartition
across every separation that crosses it. -/
theorem flower_uniform (D : Fin 3 → G.Separation) (k : ℕ)
    (flower : CornerLemma.IsFlower (weight D) k) : UniformlyCrossing D := by
  obtain ⟨squares, p, _, _, _, edges⟩ := flower
  apply (uniformlyCrossing_iff_pairwise D).mpr
  intro i j t hJ hT
  by_cases hJT : j = t
  · subst t
    rfl
  have hIJ : i ≠ j := fun eq => cross_irrefl (D j) (eq ▸ hJ)
  have hIT : i ≠ t := fun eq => cross_irrefl (D t) (eq ▸ hT)
  apply partition_of_relabel D i j t (p j == p t)
  intro x hx
  let f := faceOf D x
  have positive : 0 < weight D f :=
    card_pos.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
  apply allowed_face p f i j t hIJ hIT hJT ((separator_iff_free D x i).mp hx)
  · intro two
    exact (Nat.ne_of_gt positive) (squares f two)
  · intro one incident
    have zero := edges f one
    simp only [incident, ↓reduceIte] at zero
    exact (Nat.ne_of_gt positive) zero

end CornerSection