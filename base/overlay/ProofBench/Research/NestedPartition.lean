import ProofBench.Research.CornerCrossing

/-! Equitability balances both links. This gives a cardinality proof of Section 4.5,
Lemma 4.18, which also handles every orientation of a nested pair. -/
namespace CornerSection
open Finset CubicalDiagrams
variable {X : Type*} [Fintype X] [DecidableEq X] {G : SimpleGraph X}

private theorem separator_parts (r s : G.Separation) (a b : Bool) :
    cornerSeparator r s a b = link r s b ∪ (s.separator ∩ side r a) := by
  ext x
  cases a <;> cases b <;>
    simp [cornerSeparator, link, proper, side, SimpleGraph.Separation.separator] <;> tauto

private theorem separator_parts_disjoint (r s : G.Separation) (a b : Bool) :
    Disjoint (link r s b) (s.separator ∩ side r a) := by
  rw [Finset.disjoint_left]
  cases b <;> simp [link, proper, side, SimpleGraph.Separation.separator] <;> tauto

theorem link_balance (r s : G.Separation) (k : ℕ)
    (equity : ∀ a b, (cornerSeparator r s a b).card = k) :
    (link r s false).card = (link r s true).card := by
  have f := equity false false
  have t := equity false true
  rw [separator_parts, card_union_of_disjoint (separator_parts_disjoint _ _ _ _)] at f t
  omega

private theorem oriented_link_subset {r s t : G.Separation} {a b : Bool}
    (h : OrientedBelow s t a b) : link r s a ⊆ link r t b := by
  intro x hx
  obtain ⟨hr,hs⟩ := mem_inter.mp hx
  obtain ⟨ins,outs⟩ := mem_sdiff.mp hs
  exact mem_inter.mpr ⟨hr,mem_sdiff.mpr ⟨h.1 ins,fun hit => outs (h.2 hit)⟩⟩

theorem centre_from_links (r s : G.Separation) :
    centre r s = r.separator \ (link r s false ∪ link r s true) := by
  ext x
  have hx := mem_either s x
  simp [centre, link, proper, side, SimpleGraph.Separation.separator]
  tauto

private theorem complement_balance {r s : G.Separation} (a : Bool)
    (h : (link r s false).card = (link r s true).card) :
    (link r s a).card = (link r s (!a)).card := by
  cases a
  · exact h
  · exact h.symm

/-- In nested orientations the proper links on one side grow and those on the other
shrink. The two balance identities force equality of the actual vertex sets. -/
theorem partition_eq_of_nested {r s t : G.Separation} (hn : Nested s t)
    (hs : (link r s false).card = (link r s true).card)
    (ht : (link r t false).card = (link r t true).card) :
    partition r s = partition r t := by
  obtain ⟨a,b,fwd,back⟩ := hn
  have sub₁ : link r s a ⊆ link r t b :=
    oriented_link_subset (show OrientedBelow s t a b from ⟨fwd,back⟩)
  have sub₂ : link r t (!b) ⊆ link r s (!a) :=
    oriented_link_subset (show OrientedBelow t s (!b) (!a) from ⟨back,by simpa using fwd⟩)
  have left := complement_balance a hs
  have right := complement_balance b ht
  have h₁ := card_le_card sub₁
  have h₂ := card_le_card sub₂
  have e₁ : link r s a = link r t b := eq_of_subset_of_card_le sub₁ (by omega)
  have e₂ : link r s (!a) = link r t (!b) := (eq_of_subset_of_card_le sub₂ (by omega)).symm
  cases a <;> cases b <;> simp only [Bool.not_false, Bool.not_true] at e₁ e₂ <;>
    simp [partition, centre_from_links, e₁, e₂, Finset.union_comm, Finset.pair_comm]

private theorem three_indices : ∀ (i j t u : Fin 3), i ≠ j → i ≠ t → j ≠ t →
    u = i ∨ u = j ∨ u = t := by decide

theorem pairwise_cross_of_three {D : Fin 3 → G.Separation} {i j t : Fin 3}
    (hij : Cross (D i) (D j)) (hit : Cross (D i) (D t)) (hjt : Cross (D j) (D t)) :
    ∀ u v : Fin 3, u ≠ v → Cross (D u) (D v) := by
  have ne {m n : Fin 3} (h : Cross (D m) (D n)) : m ≠ n :=
    fun e => cross_irrefl (D n) (e ▸ h)
  intro u v huv
  have hu := three_indices i j t u (ne hij) (ne hit) (ne hjt)
  have hv := three_indices i j t v (ne hij) (ne hit) (ne hjt)
  rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;>
    subst u <;> subst v <;>
    first | exact (huv rfl).elim | assumption | exact cross_symm (by assumption)

theorem uniform_of_not_pairwise (D : Fin 3 → G.Separation) (k : ℕ) (eq : Equitable D k)
    (someNested : ¬ ∀ i j, i ≠ j → Cross (D i) (D j)) : UniformlyCrossing D := by
  apply (uniformlyCrossing_iff_pairwise D).mpr
  intro i j t hij hit
  have h : Nested (D j) (D t) := by
    by_contra notNested
    exact someNested (pairwise_cross_of_three hij hit notNested)
  exact partition_eq_of_nested h (link_balance _ _ k (eq i j hij)) (link_balance _ _ k (eq i t hit))

/-- Finite graph version of Lemma 4.18. Indices 0,1,2 denote the paper's r,s,t.
The sufficient hypotheses here are slightly weaker: crossing the first member is unnecessary. -/
theorem nested_triple_uniform (D : Fin 3 → G.Separation) (k : ℕ) (eq : Equitable D k)
    (nested : Nested (D 1) (D 2)) : UniformlyCrossing D := by
  exact uniform_of_not_pairwise _ _ eq (fun h => h 1 2 (by decide) nested)

end CornerSection
