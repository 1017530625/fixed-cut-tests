import ProofBench.Research.KeyCornerLemma
import ProofBench.Research.ApproxSeparation
import Mathlib.Data.Set.Insert

/-! Independently stated contracts for the paper's finite-graph assertions. -/
namespace CornerSection.PaperContracts
open Finset CubicalDiagrams
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def literalUniform (D : Fin 3 → G.Separation) : Prop :=
  ∀ i, ∃ X P Q : Finset V, X ∪ P ∪ Q = (D i).separator ∧
    Disjoint X P ∧ Disjoint X Q ∧ Disjoint P Q ∧
    ∀ j, Cross (D i) (D j) →
      centre (D i) (D j) = X ∧
      ((link (D i) (D j) false = P ∧ link (D i) (D j) true = Q) ∨
       (link (D i) (D j) false = Q ∧ link (D i) (D j) true = P))

omit [Fintype V] in
private theorem pair_orientation (a b c d : Finset V)
    (h : ({a,b} : Finset (Finset V)) = {c,d}) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  apply Set.pair_eq_pair_iff.mp
  simpa only [Finset.coe_insert, Finset.coe_singleton] using
    congrArg (fun z : Finset (Finset V) => (z : Set (Finset V))) h

/-- Explicitly permit empty parts and two identical empty links. -/
theorem induced_partition_contract (D : Fin 3 → G.Separation) :
    UniformlyCrossing D ↔ literalUniform D := by
  constructor
  · intro h i
    obtain ⟨_, ⟨s, rfl⟩, compatible⟩ := h i
    obtain ⟨cover, d₁, d₂, d₃⟩ := partition_parts (D i) s
    refine ⟨centre (D i) s, link (D i) s false, link (D i) s true, cover,
      d₁, d₂, d₃, ?_⟩
    intro j crossing
    have matchParts := compatible j crossing
    exact ⟨congrArg Prod.fst matchParts, pair_orientation _ _ _ _ (congrArg Prod.snd matchParts)⟩
  · intro h
    apply (uniformlyCrossing_iff_pairwise D).mpr
    intro i j t sj st
    obtain ⟨X,P,Q,_,_,_,_,compatible⟩ := h i
    obtain ⟨cj, oj⟩ := compatible j sj
    obtain ⟨ct, ot⟩ := compatible t st
    rcases oj with ⟨j₁,j₂⟩ | ⟨j₁,j₂⟩ <;> rcases ot with ⟨t₁,t₂⟩ | ⟨t₁,t₂⟩ <;>
      simp [partition, cj, ct, j₁, j₂, t₁, t₂, Finset.pair_comm]

/-- A crossing partner with all four proper corner sizes greater than ε
gives at least 2(ε+1) vertices in each proper side of r. -/
theorem breadth_from_corners (r s : G.Separation) (ε : ℕ)
    (strict : ∀ a b, ε < (properCorner r s a b).card) (a : Bool) :
    2 * (ε + 1) ≤ (proper r a).card := by
  have inside : properCorner r s a false ∪ properCorner r s a true ⊆ proper r a := by
    intro x hx
    rcases mem_union.mp hx with h | h <;> exact (mem_inter.mp h).1
  have separate : Disjoint (properCorner r s a false) (properCorner r s a true) := by
    rw [Finset.disjoint_left]
    simp [properCorner, proper, side]
    tauto
  have first := strict a false
  have second := strict a true
  have count := card_le_card inside
  rw [card_union_of_disjoint separate] at count
  omega

abbrev Broad (s : G.Separation) (q : ℕ) :=
  q ≤ min (s.A \ s.B).card (s.B \ s.A).card

/-- Original finite-graph hypotheses of Lemma 4.15 as a direct specialization. -/
theorem lemma415 (D : Fin 3 → G.Separation) (q k : ℕ)
    (_graph : Unbreakable G q (k - 1)) (_order : ∀ i, (D i).order = k)
    (_broad : ∀ i, Broad (D i) q) (eq : Equitable D k)
    (criss : CrissCompatible D (2 * q + k)) (pairs : ∀ i j, i ≠ j → Cross (D i) (D j)) :
    ∀ p r, CornerLemma.Adj p r → p ∈ largeCorners D q k ∨ r ∈ largeCorners D q k :=
  large_corner_cover D q k eq criss pairs

/-- Frozen cut value and the three coordinate cuts of Lemma 4.12. -/
theorem lemma412 (D : Fin 3 → G.Separation) (k : ℕ) (order : ∀ i, (D i).order = k) :
    ∀ i, CornerLemma.cutValue (weight D) (coordinateSide i false) = k := by
  intro i
  rw [← CubicalDiagrams.P118.cutValue_eq, coordinate_order, order i]

/-- Realized sides on every corner cut as well as the paper's cut-weight equality. -/
theorem lemma413 (D : Fin 3 → G.Separation) (S : Finset CornerLemma.Vertex) :
    (∀ x, x ∈ (lift D S).A ↔ ∃ p ∈ S, ∀ i, x ∈ side (D i) (p i)) ∧
    (∀ x, x ∈ (lift D S).B ↔ ∃ p ∈ univ \ S, ∀ i, x ∈ side (D i) (p i)) ∧
    (lift D S).order = CornerLemma.cutValue (weight D) S := by
  exact ⟨mem_aggregate_iff _ _, mem_aggregate_iff _ _,
    (order_lift D S).trans (CubicalDiagrams.P118.cutValue_eq _ _)⟩

theorem lemma416 (D : Fin 3 → G.Separation) (q k : ℕ)
    (graph : Unbreakable G q (k-1)) (_order : ∀ i, (D i).order = k)
    (S : Finset CornerLemma.Vertex)
    (left : ∃ p ∈ largeCorners D q k, p ∈ S) (right : ∃ p ∈ largeCorners D q k, p ∉ S) :
    k ≤ CornerLemma.cutValue (weight D) S := by
  rw [← CubicalDiagrams.P118.cutValue_eq]
  exact large_corner_cut q k graph D S left right

/-- Ordinary oriented nesting as in the displayed Lemma 4.18 hypothesis s ≤ t. -/
theorem lemma418 (D : Fin 3 → G.Separation) (k : ℕ) (_orders : ∀ i, (D i).order = k)
    (eq : Equitable D k) (_rs : Cross (D 0) (D 1)) (_rt : Cross (D 0) (D 2))
    (AC : (D 1).A ⊆ (D 2).A) (DB : (D 2).B ⊆ (D 1).B) : literalUniform D :=
  (induced_partition_contract D).mp (nested_triple_uniform D k eq ⟨false,false,AC,DB⟩)

theorem lemma417 (D : Fin 3 → G.Separation) (k : ℕ) (_order : ∀ i, (D i).order = k)
    (flower : CornerLemma.IsFlower (weight D) k) : literalUniform D :=
  (induced_partition_contract D).mp (flower_uniform D k flower)

theorem lemma414 (D : Fin 3 → G.Separation) (q k : ℕ)
    (graph : Unbreakable G q (k-1)) (orders : ∀ i, (D i).order = k)
    (eq : Equitable D k) (strict : CrissCompatible D (2*q+k)) : literalUniform D :=
  (induced_partition_contract D).mp (key_lemma_4_14 D q k graph orders eq strict)

end CornerSection.PaperContracts

#print axioms CornerSection.PaperContracts.induced_partition_contract
#print axioms CornerSection.PaperContracts.breadth_from_corners
#print axioms CornerSection.PaperContracts.lemma412
#print axioms CornerSection.PaperContracts.lemma413
#print axioms CornerSection.PaperContracts.lemma414
#print axioms CornerSection.PaperContracts.lemma415
#print axioms CornerSection.PaperContracts.lemma416
#print axioms CornerSection.PaperContracts.lemma417
#print axioms CornerSection.PaperContracts.lemma418
