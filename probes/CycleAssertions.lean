import ProofBench.Research.PaperKeyBridge
import ProofBench.PROBLEMS.P118.GeneralGraphCuts
import NontrivialNestedCycle

namespace ManuscriptCycleCheck

open Finset CornerSection

#check PaperCorner.key_lemma_4_14
#check CornerSection.key_lemma_4_14
#print PaperCorner.Crosses
#print PaperCorner.UnbreakableBelow
#print PaperCorner.Equitable
#print PaperCorner.CrissCompatible
#print PaperCorner.Uniform
#print PaperCorner.Induces
#check CornerSection.nested_triple_uniform
#check CornerSection.flower_uniform
#check CornerSection.Cycle24.deletion_preconnected
#check CornerSection.Cycle24.unbreakable
#check CornerSection.Cycle24.crosses
#check CornerSection.Cycle24.orders
#check CornerSection.Cycle24.proper_sizes
#check CornerSection.Cycle24.partition_sizes
#check CornerSection.Cycle24.equitable
#check CornerSection.Cycle24.criss
#check CornerSection.Cycle24.nonzero_profile
#check CornerSection.Cycle24.flower
#check CornerSection.NestedCycle24.crossing_pattern
#check CornerSection.NestedCycle24.literal_nesting
#check CornerSection.NestedCycle24.nested
#check CornerSection.NestedCycle24.orders
#check CornerSection.NestedCycle24.equitable
#check CornerSection.NestedCycle24.criss
#check CornerSection.NestedCycle24.partitions
#check CornerSection.NestedCycle24.via_nested
#check CornerSection.NestedCycle24.via_key
#check CornerArbitraryCuts.on_star_iff_complete
#check CornerArbitraryCuts.connected_iff_complete
#check CornerArbitraryCuts.graph_iff_complete
#print ConnectedCornerTests.SufficientOn

theorem strict_below_zero {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (q : ℕ) :
    PaperCorner.UnbreakableBelow G q 0 := by
  intro s h
  omega

theorem strict_below_positive {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (q k : ℕ) (positive : 0 < k) :
    PaperCorner.UnbreakableBelow G q k ↔ CubicalDiagrams.Unbreakable G q (k-1) := by
  constructor <;> intro h s bound <;> exact h s (by omega)

theorem uniform_of_order_zero {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (D : Fin 3 → G.Separation) (orders : ∀ i, (D i).order = 0) : PaperCorner.Uniform D := by
  intro i
  have empty : (D i).separator = ∅ := Finset.card_eq_zero.mp (orders i)
  refine ⟨∅, ∅, ∅, ?_, by simp, by simp, by simp, ?_⟩
  · simp [empty]
  · intro j _
    simp [PaperCorner.Induces, empty]

private theorem crosses_agree {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (r s : G.Separation) : PaperCorner.Crosses r s ↔ CornerSection.Cross r s := by
  unfold PaperCorner.Crosses CornerSection.Cross CornerSection.Nested CornerSection.OrientedBelow
  simp only [Bool.exists_bool, CubicalDiagrams.side, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true]
  tauto

private theorem uniform_two (D : Fin 3 → Cycle24.host.Separation)
    (orders : ∀ i, (D i).order = 2) (fair : CornerSection.Equitable D 2)
    (large : CornerSection.CrissCompatible D (2 * 0 + 2)) : PaperCorner.Uniform D := by
  apply PaperCorner.key_lemma_4_14 D 0 2 _ orders
  · intro i j h a b
    have eq := fair i j ((crosses_agree _ _).mp h) a b
    cases a <;> cases b <;> exact eq
  · intro i j h a b
    have bound := large i j ((crosses_agree _ _).mp h) a b
    cases a <;> cases b <;> exact bound
  · intro s h
    exact Cycle24.unbreakable s (by omega)

theorem all_crossing_uniform : PaperCorner.Uniform Cycle24.diagram :=
  uniform_two _ Cycle24.orders Cycle24.equitable Cycle24.criss

theorem mixed_uniform : PaperCorner.Uniform NestedCycle24.D :=
  uniform_two _ NestedCycle24.orders NestedCycle24.equitable NestedCycle24.criss

set_option maxRecDepth 25000
set_option maxHeartbeats 7000000

/-- Relative to coordinate zero, the j=1 and j=2 matrices have rows (3,7) and (7,3). -/
theorem mixed_open_corners : ∀ (j : Fin 3), j ≠ 0 → ∀ a b : Bool,
    (properCorner (NestedCycle24.D 0) (NestedCycle24.D j) a b).card =
      if (j = 1 ∧ b = false) ∨ (j = 2 ∧ b = true) then 3 else 7 := by decide

private def corner (n : ℕ) : CornerLemma.Vertex := fun i => n.testBit (2-i.val)

private abbrev spans (f : CornerLemma.Face) (a b : ℕ) : Prop :=
  CornerLemma.InFace (corner a) f ∧ CornerLemma.InFace (corner b) f

/-- The six positive edge faces, each of weight one, run through 0,2,3,7,6,4 in order. -/
theorem mixed_six_edge_weights : ∀ f : CornerLemma.Face, CornerLemma.dim f = 1 →
    CubicalDiagrams.weight NestedCycle24.D f = if spans f 0 2 ∨ spans f 2 3 ∨ spans f 3 7 ∨
      spans f 7 6 ∨ spans f 6 4 ∨ spans f 4 0 then 1 else 0 := by decide

theorem mixed_isolated_corners : ∀ v : CornerLemma.Vertex,
    (∀ f : CornerLemma.Face, CornerLemma.dim f = 1 → CornerLemma.InFace v f →
      CubicalDiagrams.weight NestedCycle24.D f = 0) ↔ v = corner 1 ∨ v = corner 5 := by decide

theorem mixed_isolates_adjacent : CornerLemma.Adj (corner 1) (corner 5) := by decide

/-- At least one edge incident with either proposed pole carries positive mass. -/
theorem mixed_positive_at_poles : ∀ v : CornerLemma.Vertex, ∃ f : CornerLemma.Face,
    CornerLemma.dim f = 1 ∧ (CornerLemma.InFace v f ∨ CornerLemma.InFace (fun i => !(v i)) f) ∧
    0 < CubicalDiagrams.weight NestedCycle24.D f := by decide

theorem mixed_not_flower (k : ℕ) : ¬ CornerLemma.IsFlower (CubicalDiagrams.weight NestedCycle24.D) k := by
  rintro ⟨_, v, level, _, _, edge⟩
  obtain ⟨f, dim, pole, pos⟩ := mixed_positive_at_poles v
  have zero : CubicalDiagrams.weight NestedCycle24.D f = 0 := by simpa [pole] using edge f dim
  exact (Nat.ne_of_gt pos) zero

theorem mixed_uniform_without_two_flower : PaperCorner.Uniform NestedCycle24.D ∧
    ¬ CornerLemma.IsFlower (CubicalDiagrams.weight NestedCycle24.D) 2 := ⟨mixed_uniform, mixed_not_flower 2⟩

theorem fixed_star_iff_graphs (S : Finset (Finset CornerLemma.Vertex)) :
    ConnectedCornerTests.SufficientOn ConnectedCornerTests.host S ↔ GraphCornerTests.Sufficient S :=
  (CornerArbitraryCuts.on_star_iff_complete S).trans (CornerArbitraryCuts.graph_iff_complete S).symm

#check strict_below_zero
#check strict_below_positive
#check uniform_of_order_zero
#check all_crossing_uniform
#check mixed_uniform
#check mixed_open_corners
#check mixed_six_edge_weights
#check mixed_isolated_corners
#check mixed_isolates_adjacent
#check mixed_positive_at_poles
#check mixed_not_flower
#check mixed_uniform_without_two_flower
#check fixed_star_iff_graphs

#print axioms PaperCorner.key_lemma_4_14
#print axioms CornerSection.key_lemma_4_14
#print axioms CornerSection.nested_triple_uniform
#print axioms CornerSection.flower_uniform
#print axioms CornerSection.Cycle24.deletion_preconnected
#print axioms CornerSection.Cycle24.unbreakable
#print axioms CornerSection.Cycle24.crosses
#print axioms CornerSection.Cycle24.orders
#print axioms CornerSection.Cycle24.proper_sizes
#print axioms CornerSection.Cycle24.partition_sizes
#print axioms CornerSection.Cycle24.equitable
#print axioms CornerSection.Cycle24.criss
#print axioms CornerSection.Cycle24.nonzero_profile
#print axioms CornerSection.Cycle24.flower
#print axioms CornerSection.NestedCycle24.crossing_pattern
#print axioms CornerSection.NestedCycle24.literal_nesting
#print axioms CornerSection.NestedCycle24.nested
#print axioms CornerSection.NestedCycle24.orders
#print axioms CornerSection.NestedCycle24.equitable
#print axioms CornerSection.NestedCycle24.criss
#print axioms CornerSection.NestedCycle24.partitions
#print axioms CornerSection.NestedCycle24.via_nested
#print axioms CornerSection.NestedCycle24.via_key
#print axioms CornerArbitraryCuts.on_star_iff_complete
#print axioms CornerArbitraryCuts.connected_iff_complete
#print axioms CornerArbitraryCuts.graph_iff_complete
#print axioms ManuscriptCycleCheck.strict_below_zero
#print axioms ManuscriptCycleCheck.strict_below_positive
#print axioms ManuscriptCycleCheck.uniform_of_order_zero
#print axioms ManuscriptCycleCheck.all_crossing_uniform
#print axioms ManuscriptCycleCheck.mixed_uniform
#print axioms ManuscriptCycleCheck.mixed_open_corners
#print axioms ManuscriptCycleCheck.mixed_six_edge_weights
#print axioms ManuscriptCycleCheck.mixed_isolated_corners
#print axioms ManuscriptCycleCheck.mixed_isolates_adjacent
#print axioms ManuscriptCycleCheck.mixed_positive_at_poles
#print axioms ManuscriptCycleCheck.mixed_not_flower
#print axioms ManuscriptCycleCheck.mixed_uniform_without_two_flower
#print axioms ManuscriptCycleCheck.fixed_star_iff_graphs

end ManuscriptCycleCheck
