import ProofBench.Research.CubicalP118
import ProofBench.Research.LargeCornerCuts

/-! Flower rigidity from the graph's own large corner regions. -/
namespace CubicalDiagrams.P118

variable {X : Type*} [Fintype X] [DecidableEq X] {G : SimpleGraph X}

/-- If the large inclusive corners cover every cube edge, a triple of
order-k separations of a (q,k-1)-unbreakable finite graph yields a k-flower.
The large-corner cover is an explicit hypothesis as in the use of Lemma 4.15. -/
theorem flower_of_large_corner_cover (D : Fin 3 → G.Separation) (q k : ℕ)
    (unbreakable : Unbreakable G q (k - 1)) (coord : ∀ i, (D i).order = k)
    (cover : ∀ p r, CornerLemma.Adj p r →
      p ∈ largeCorners D q k ∨ r ∈ largeCorners D q k) :
    CornerLemma.IsFlower (weight D) k := by
  apply flower_of_order_bounds D k coord (largeCorners D q k) cover
  intro A left right
  rw [order_lift]
  exact large_corner_cut q k unbreakable D A left right

end CubicalDiagrams.P118
