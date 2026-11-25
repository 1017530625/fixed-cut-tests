import ProofBench.Research.CubicalDiagrams
import ProofBench.PROBLEMS.P118.SeparationDiagrams

/-! Compatibility with the original P118 cube and its three-separation diagram. -/

namespace CubicalDiagrams.P118

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {G : SimpleGraph X}

theorem weight_eq (D : Fin 3 → G.Separation) :
    CubicalDiagrams.weight D = SeparationDiagrams.weight D := rfl

theorem aggregate_eq (D : Fin 3 → G.Separation) (A : Finset CornerLemma.Vertex) :
    CubicalDiagrams.aggregate D A = SeparationDiagrams.aggregate D A := by
  ext x
  exact (CubicalDiagrams.mem_aggregate_iff D A x).trans
    (SeparationDiagrams.mem_aggregate_iff D A x).symm

theorem lift_eq (D : Fin 3 → G.Separation) (A : Finset CornerLemma.Vertex) :
    CubicalDiagrams.lift D A = SeparationDiagrams.lift D A := by
  have extSides (s t : G.Separation) (ha : s.A = t.A) (hb : s.B = t.B) : s = t := by
    cases s
    cases t
    congr
  exact extSides _ _ (aggregate_eq D A) (aggregate_eq D _)

/-- In three dimensions both cut functions count the same faces for every
weighting. Realize the weighting on the edgeless graph and compare the two
formulas for the order of the same lifted separation. -/
theorem cutValue_eq (w : CornerLemma.Face → ℕ) (A : Finset CornerLemma.Vertex) :
    CubicalDiagrams.cutValue w A = CornerLemma.cutValue w A := by
  calc
    CubicalDiagrams.cutValue w A = (CubicalDiagrams.lift (diagram w) A).order := by
      rw [order_lift, weight_diagram]
    _ = (SeparationDiagrams.lift (diagram w) A).order :=
      congrArg (fun s => s.order) (lift_eq (diagram w) A)
    _ = CornerLemma.cutValue w A := by
      rw [SeparationDiagrams.order_lift, ← weight_eq, weight_diagram]

/-- Apply the frozen P118 theorem directly using the generic lifted orders. -/
theorem flower_of_order_bounds (D : Fin 3 → G.Separation) (k : ℕ)
    (coords : ∀ i, (D i).order = k) (R : Finset CornerLemma.Vertex)
    (cover : ∀ p q, CornerLemma.Adj p q → p ∈ R ∨ q ∈ R)
    (lower : ∀ A : Finset CornerLemma.Vertex, (∃ p ∈ R, p ∈ A) →
      (∃ q ∈ R, q ∉ A) → k ≤ (CubicalDiagrams.lift D A).order) :
    CornerLemma.IsFlower (CubicalDiagrams.weight D) k := by
  refine _root_.P118 _ k ?_ R cover ?_
  · intro i
    rw [← cutValue_eq]
    exact (coordinate_order D i).trans (coords i)
  · intro A h₁ h₂
    rw [← cutValue_eq, ← order_lift]
    exact lower A h₁ h₂

end CubicalDiagrams.P118
