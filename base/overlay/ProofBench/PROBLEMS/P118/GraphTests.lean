import ProofBench.PROBLEMS.P118.RealizeWeights
import ProofBench.PROBLEMS.P118.MinimumDesigns

namespace GraphCornerTests

open Finset CornerLemma CornerCutLowerBound SeparationDiagrams RealizeWeights

/-- A test family works on triples of finite graph separations. All measured
    quantities in the hypotheses are orders of actual separations. -/
def Sufficient (S : Finset (Finset Vertex)) : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (G : SimpleGraph X)
    (D : Fin 3 → G.Separation) (R : Finset Vertex) (k : ℕ),
    (∀ i, (D i).order = k) →
    (∀ u v, Adj u v → u ∈ R ∨ v ∈ R) →
    (∀ u ∈ R, k ≤ (lift D {u}).order) →
    (∀ A ∈ S, (∃ u ∈ R, u ∈ A) → (∃ v ∈ R, v ∉ A) → k ≤ (lift D A).order) →
    IsFlower (weight D) k

/-- Every diagram yields a weighting, and every weighting is realized by
    a finite diagram. This equivalence also covers test sides of other shapes. -/
theorem iff_weighted (S : Finset (Finset Vertex)) :
    Sufficient S ↔ CubeTransversals.Sufficient S := by
  constructor
  · intro graph w k R coord cover atom pair
    have order (i : Fin 3) : (diagram w i).order = k := by
      rw [← coordinate_order, weight_diagram]
      exact coord i
    have single (u : Vertex) (hu : u ∈ R) : k ≤ (lift (diagram w) {u}).order := by
      rw [order_lift, weight_diagram]
      exact atom u hu
    have check (A : Finset Vertex) (hA : A ∈ S)
        (hu : ∃ u ∈ R, u ∈ A) (hv : ∃ v ∈ R, v ∉ A) :
        k ≤ (lift (diagram w) A).order := by
      rw [order_lift, weight_diagram]
      exact pair A hA hu hv
    simpa only [weight_diagram] using graph (Carrier w) ⊥ (diagram w) R k order cover single check
  · intro weighted X _ _ G D R k coord cover atom pair
    apply weighted (weight D) k R (fun i => (coordinate_order D i).trans (coord i)) cover
    · intro u hu
      rw [← order_lift]
      exact atom u hu
    · intro A hA hu hv
      rw [← order_lift]
      exact pair A hA hu hv

theorem iff_hitsAll (S : Finset (Finset Vertex)) (pairs : ∀ A ∈ S, AdjacentSide A) :
    Sufficient S ↔ HitsAll S :=
  (iff_weighted S).trans (CubeTransversals.sufficient_iff_hitsAll S pairs)

theorem four_iff_listed (S : Finset (Finset Vertex)) (card : S.card = 4)
    (pairs : ∀ A ∈ S, AdjacentSide A) :
    Sufficient S ↔ S ∈ CubeMinimumDesigns.nineDesigns :=
  (iff_weighted S).trans (CubeMinimumDesigns.sufficient_four_iff S card pairs)

theorem at_least_four (S : Finset (Finset Vertex)) (pairs : ∀ A ∈ S, AdjacentSide A)
    (sufficient : Sufficient S) : 4 ≤ S.card :=
  CubeMinimumDesigns.at_least_four_tests S pairs ((iff_weighted S).mp sufficient)

end GraphCornerTests
