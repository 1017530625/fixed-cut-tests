import ProofBench.PROBLEMS.P118.SeparationDiagrams
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Powerset

/-! Realization of natural cube-face weights by three separations of a finite edgeless graph. -/

namespace RealizeWeights
open CornerLemma CornerCutLowerBound SeparationDiagrams Finset

/-- One graph vertex for each unit of mass at a face. -/
abbrev Carrier (w : Face → ℕ) := (f : Face) × Fin (w f)

/-- Take the edgeless graph. At coordinate i, a free face belongs to both sides. -/
def diagram (w : Face → ℕ) (i : Fin 3) : (⊥ : SimpleGraph (Carrier w)).Separation where
  A := univ.filter fun x => x.1 i ≠ some true
  B := univ.filter fun x => x.1 i ≠ some false
  union_eq := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    cases h : x.1 i with
    | none => simp
    | some b => cases b <;> simp
  no_edge_across := by
    intro u v h
    exact False.elim h

private def fiberEquiv (w : Face → ℕ) (f : Face) :
    {x : Carrier w // x.1 = f} ≃ Fin (w f) where
  toFun := fun ⟨⟨g, a⟩, h⟩ => h ▸ a
  invFun := fun a => ⟨⟨f, a⟩, rfl⟩
  left_inv := by rintro ⟨⟨g, a⟩, h⟩; cases h; rfl
  right_inv := fun _ => rfl

private theorem fiberCard (w : Face → ℕ) (f : Face) :
    (univ.filter fun x : Carrier w => x.1 = f).card = w f := by
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr (fiberEquiv w f)).trans (Fintype.card_fin _)


/-- The graph visualization recovers the label of each graph vertex. -/
theorem faceOf_diagram (w : Face → ℕ) (x : Carrier w) :
    faceOf (diagram w) x = x.1 := by
  funext i
  cases h : x.1 i with
  | none => simp [faceOf, diagram, h]
  | some b => cases b <;> simp [faceOf, diagram, h]

/-- Surjectivity of visualization: all 27 prescribed fiber sizes are attained. -/
theorem weight_diagram (w : Face → ℕ) : weight (diagram w) = w := by
  funext f
  unfold weight
  simp only [faceOf_diagram]
  exact fiberCard w f

theorem exists_edgeless_realization (w : Face → ℕ) :
    ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U)
      (D : Fin 3 → (⊥ : SimpleGraph U).Separation), weight D = w :=
  ⟨Carrier w, inferInstance, inferInstance, diagram w, weight_diagram w⟩

/-- For each of the eight matchings, every edge test outside it and all tests at
the vertices of a cube cover can pass on a genuine triple of graph separations,
while the observed face weights fail the 1-flower conclusion. -/
theorem graph_obstruction (j : Fin 8) :
    ∃ (w : Face → ℕ) (R : Finset Vertex),
      (∀ i, (diagram w i).order = 1) ∧
      (∀ u v, Adj u v → u ∈ R ∨ v ∈ R) ∧
      (∀ u ∈ R, 1 ≤ (lift (diagram w) {u}).order) ∧
      (∀ u v, Adj u v → {u, v} ∉ AlternatingMatching j →
        1 ≤ (lift (diagram w) {u, v}).order) ∧
      ¬ IsFlower (weight (diagram w)) 1 := by
  classical
  let S : Finset (Finset Vertex) :=
    univ.filter fun A => AdjacentSide A ∧ A ∉ AlternatingMatching j
  have pairs : ∀ A ∈ S, AdjacentSide A := fun _ h => (mem_filter.mp h).2.1
  have missed : ¬ HitsAll S := by
    intro hit
    obtain ⟨A, hA, hS⟩ := hit j
    exact (mem_filter.mp hS).2.2 hA
  obtain ⟨w, R, coords, cover, atoms, edges, bad⟩ :=
    counterexample_of_not_hitsAll S pairs missed
  refine ⟨w, R, ?_, cover, ?_, ?_, ?_⟩
  · intro i
    rw [← coordinate_order, weight_diagram]
    exact coords i
  · intro u hu
    rw [order_lift, weight_diagram]
    exact atoms u hu
  · intro u v huv hmiss
    rw [order_lift, weight_diagram]
    exact edges _ (mem_filter.mpr ⟨mem_univ _, ⟨u, v, huv, rfl⟩, hmiss⟩)
  · simpa only [weight_diagram] using bad

end RealizeWeights

#print axioms RealizeWeights.faceOf_diagram
#print axioms RealizeWeights.weight_diagram
#print axioms RealizeWeights.exists_edgeless_realization
#print axioms RealizeWeights.graph_obstruction
