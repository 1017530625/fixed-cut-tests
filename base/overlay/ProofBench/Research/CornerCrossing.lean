import ProofBench.Research.LargeCornersP118
import ProofBench.Research.CubicalExamples

/-! Oriented separations, corners, and the tripartition induced on a separator.
Definitions follow Sections 3.1 and 4.2–4.5 of arXiv:2611.01772v1. -/

namespace CornerSection

open Finset CubicalDiagrams

variable {X : Type*} [Fintype X] [DecidableEq X] {G : SimpleGraph X}

theorem mem_either (s : G.Separation) (x : X) : x ∈ s.A ∨ x ∈ s.B := by
  apply mem_union.mp
  rw [s.union_eq]
  exact mem_univ _

def proper (s : G.Separation) (b : Bool) : Finset X := side s b \ side s (!b)

def link (r s : G.Separation) (b : Bool) : Finset X := r.separator ∩ proper s b

def centre (r s : G.Separation) : Finset X := r.separator ∩ s.separator

/-- The centre is distinguished; the two links have no ordering. Empty parts are allowed. -/
def partition (r s : G.Separation) : Finset X × Finset (Finset X) :=
  (centre r s, {link r s false, link r s true})

theorem partition_parts (r s : G.Separation) :
    centre r s ∪ link r s false ∪ link r s true = r.separator ∧
    Disjoint (centre r s) (link r s false) ∧ Disjoint (centre r s) (link r s true) ∧
    Disjoint (link r s false) (link r s true) := by
  constructor
  · ext x
    have hx := mem_either s x
    simp [centre, link, proper, side, SimpleGraph.Separation.separator]
    tauto
  · simp only [Finset.disjoint_left]
    simp [centre, link, proper, side, SimpleGraph.Separation.separator] <;> tauto

def OrientedBelow (s t : G.Separation) (a b : Bool) : Prop :=
  side s a ⊆ side t b ∧ side t (!b) ⊆ side s (!a)

/-- Either separation can be flipped before comparing them. -/
def Nested (s t : G.Separation) : Prop := ∃ a b, OrientedBelow s t a b

def Cross (s t : G.Separation) : Prop := ¬ Nested s t

theorem nested_symm {s t : G.Separation} (h : Nested s t) : Nested t s := by
  obtain ⟨a,b,forward,back⟩ := h
  exact ⟨!b,!a,back,by simpa using forward⟩

theorem cross_symm {s t : G.Separation} (h : Cross s t) : Cross t s :=
  fun nested => h (nested_symm nested)

theorem cross_irrefl (s : G.Separation) : ¬ Cross s s :=
  fun h => h ⟨false,false,fun _ hx => hx,fun _ hx => hx⟩

def properCorner (r s : G.Separation) (a b : Bool) : Finset X := proper r a ∩ proper s b

/-- Separator of the oriented corner (intersection of chosen sides, union of opposite sides). -/
def cornerSeparator (r s : G.Separation) (a b : Bool) : Finset X :=
  (side r a ∩ side s b) ∩ (side r (!a) ∪ side s (!b))

def Equitable (D : Fin 3 → G.Separation) (k : ℕ) : Prop :=
  ∀ i j, Cross (D i) (D j) → ∀ a b, (cornerSeparator (D i) (D j) a b).card = k

def CrissCompatible (D : Fin 3 → G.Separation) (ε : ℕ) : Prop :=
  ∀ i j, Cross (D i) (D j) → ∀ a b, ε < (properCorner (D i) (D j) a b).card

/-- Each separator has a realized centre/unordered-pair partition shared by all crossers. -/
def UniformlyCrossing (D : Fin 3 → G.Separation) : Prop :=
  ∀ i, ∃ P : Finset X × Finset (Finset X),
    (∃ s : G.Separation, partition (D i) s = P) ∧
    ∀ j, Cross (D i) (D j) → partition (D i) (D j) = P

theorem uniformlyCrossing_iff_pairwise (D : Fin 3 → G.Separation) :
    UniformlyCrossing D ↔ ∀ i j t, Cross (D i) (D j) → Cross (D i) (D t) →
      partition (D i) (D j) = partition (D i) (D t) := by
  classical
  constructor
  · intro h i j t hj ht
    obtain ⟨_,_,p⟩ := h i
    exact (p j hj).trans (p t ht).symm
  · intro h i
    by_cases ex : ∃ j, Cross (D i) (D j)
    · obtain ⟨t,ht⟩ := ex
      exact ⟨partition (D i) (D t), ⟨D t,rfl⟩, fun j hj => h i j t hj ht⟩
    · exact ⟨partition (D i) (D i), ⟨D i,rfl⟩, fun j hj => (ex ⟨j,hj⟩).elim⟩

end CornerSection
