import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Separation

/-! A finite-graph specification for Key Lemma 4.14 of Bourneuf, Carmesin,
Kurkofka and Planken (arXiv:2611.01772v1, §4.5). Only the upstream vertex
separation type and elementary finite sets are used here. -/

namespace PaperCorner

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- No orientation of one separation lies below an orientation of the other. -/
def Crosses (r s : G.Separation) : Prop :=
  ¬ ((r.A ⊆ s.A ∧ s.B ⊆ r.B) ∨ (r.A ⊆ s.B ∧ s.A ⊆ r.B) ∨
     (r.B ⊆ s.A ∧ s.B ⊆ r.A) ∨ (r.B ⊆ s.B ∧ s.A ⊆ r.A))

/-- Either orientation can be used when forming each of the four corners. -/
def oriented (r : G.Separation) (reverse : Bool) : G.Separation :=
  if reverse then r.flip else r

/-- The private intersection is the vertex set of the open corner. -/
def openCorner (r s : G.Separation) : Finset V :=
  (r.A \ r.B) ∩ (s.A \ s.B)

/-- Intersection of the two sides of the oriented corner separation
whose sides are the intersection of the chosen sides and the union of the opposite sides. -/
def cornerBoundary (r s : G.Separation) : Finset V :=
  (r.A ∩ s.A) ∩ (r.B ∪ s.B)

/-- Every separation of order strictly below k has a private side of size at most q.
For positive k this is (q,k−1)-unbreakability. For k=0 the quantification is empty. -/
def UnbreakableBelow (G : SimpleGraph V) (q k : ℕ) : Prop :=
  ∀ s : G.Separation, s.order < k → (s.A \ s.B).card ≤ q ∨ (s.B \ s.A).card ≤ q

def Equitable (D : Fin 3 → G.Separation) (k : ℕ) : Prop :=
  ∀ i j, Crosses (D i) (D j) → ∀ a b : Bool,
    (cornerBoundary (oriented (D i) a) (oriented (D j) b)).card = k

def CrissCompatible (D : Fin 3 → G.Separation) (threshold : ℕ) : Prop :=
  ∀ i j, Crosses (D i) (D j) → ∀ a b : Bool,
    threshold < (openCorner (oriented (D i) a) (oriented (D j) b)).card

/-- The centre is distinguished. Either ordering of the two actual links is accepted. -/
def Induces (r s : G.Separation) (centre left right : Finset V) : Prop :=
  r.separator ∩ s.separator = centre ∧
    ((r.separator ∩ (s.A \ s.B) = left ∧ r.separator ∩ (s.B \ s.A) = right) ∨
     (r.separator ∩ (s.A \ s.B) = right ∧ r.separator ∩ (s.B \ s.A) = left))

/-- One distinguished centre and a pair of links for each separator. Their union
is the separator, the three sets are pairwise disjoint, and every crossing member
induces them. Empty parts are allowed. Vertex sets, not only cardinalities, agree. -/
def Uniform (D : Fin 3 → G.Separation) : Prop :=
  ∀ i, ∃ centre left right : Finset V,
    centre ∪ left ∪ right = (D i).separator ∧
    Disjoint centre left ∧ Disjoint centre right ∧ Disjoint left right ∧
    ∀ j, Crosses (D i) (D j) → Induces (D i) (D j) centre left right

end PaperCorner
