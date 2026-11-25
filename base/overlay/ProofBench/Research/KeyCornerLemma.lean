import ProofBench.Research.FlowerPartition
import ProofBench.Research.NestedPartition

/-!
# The 3D Corner Lemma for finite simple graphs

Lemmas 4.15 and 4.14 of Bourneuf, Carmesin, Kurkofka and Planken.
The original large-corner set is determined by the graph diagram.
-/
namespace CornerSection

open CubicalDiagrams Finset
variable {X : Type*} [Fintype X] [DecidableEq X] {G : SimpleGraph X}

private theorem shared_indices : ∀ p r : CornerLemma.Vertex, CornerLemma.Adj p r →
    ∃ i j t : Fin 3, i ≠ j ∧ (∀ u, u = i ∨ u = j ∨ u = t) ∧
      p i = r i ∧ p j = r j ∧ p t ≠ r t := by decide

private theorem split_side (s : G.Separation) (b c : Bool) (h : b ≠ c) (x : X) :
    x ∈ side s b ∨ x ∈ side s c := by
  cases b <;> cases c <;> simp_all [side, or_comm, mem_either s x]

private theorem region_cover (D : Fin 3 → G.Separation) (p r : CornerLemma.Vertex)
    (i j t : Fin 3) (indices : ∀ u, u = i ∨ u = j ∨ u = t)
    (pi : p i = r i) (pj : p j = r j) (different : p t ≠ r t) :
    side (D i) (p i) ∩ side (D j) (p j) ⊆ region D p ∪ region D r := by
  intro x hx
  obtain ⟨hi, hj⟩ := mem_inter.mp hx
  rcases split_side (D t) (p t) (r t) different x with hp | hr
  · apply mem_union_left
    apply (mem_region D p x).mpr
    intro u
    rcases indices u with e | e | e
    · simpa only [e] using hi
    · simpa only [e] using hj
    · simpa only [e] using hp
  · apply mem_union_right
    apply (mem_region D r x).mpr
    intro u
    rcases indices u with e | e | e
    · simpa only [e, ← pi] using hi
    · simpa only [e, ← pj] using hj
    · simpa only [e] using hr

private theorem inclusive_size (s t : G.Separation) (a b : Bool) :
    (side s a ∩ side t b).card =
       (properCorner s t a b).card + (cornerSeparator s t a b).card := by
  have cover : side s a ∩ side t b = properCorner s t a b ∪ cornerSeparator s t a b := by
    ext x
    cases a <;> cases b <;>
      simp [properCorner, proper, cornerSeparator, side] <;> tauto
  have disjoint : Disjoint (properCorner s t a b) (cornerSeparator s t a b) := by
    rw [Finset.disjoint_left]
    cases a <;> cases b <;>
      simp [properCorner, proper, cornerSeparator, side] <;> tauto
  rw [cover, card_union_of_disjoint disjoint]

/-- Lemma 4.15. Pairwise crossing, equitability and strict corner sizes
suffice for the cube cover. This proof does not require unbreakability. -/
theorem large_corner_cover (D : Fin 3 → G.Separation) (q k : ℕ)
    (eq : Equitable D k) (criss : CrissCompatible D (2 * q + k))
    (pairs : ∀ i j, i ≠ j → Cross (D i) (D j)) :
    ∀ p r, CornerLemma.Adj p r → p ∈ largeCorners D q k ∨ r ∈ largeCorners D q k := by
  intro p r adjacent
  obtain ⟨i, j, t, distinct, indices, pi, pj, different⟩ := shared_indices p r adjacent
  have cross := pairs i j distinct
  have equity := eq i j cross (p i) (p j)
  have strict := criss i j cross (p i) (p j)
  have split := inclusive_size (D i) (D j) (p i) (p j)
  have contained := (card_le_card (region_cover D p r i j t indices pi pj different)).trans
    (card_union_le (region D p) (region D r))
  simp only [largeCorners, mem_filter, mem_univ, true_and]
  omega

/-- Key Lemma 4.14. An equitable, (2q+k)-criss-compatible triple of
order-k vertex separations in a (q,k-1)-unbreakable finite simple graph
is uniformly crossing. Each pair that crosses the same separator induces
the same actual centre and the same unordered pair of actual links. -/
theorem key_lemma_4_14 (D : Fin 3 → G.Separation) (q k : ℕ)
    (unbreakable : Unbreakable G q (k - 1)) (orders : ∀ i, (D i).order = k)
    (equity : Equitable D k) (criss : CrissCompatible D (2 * q + k)) :
    UniformlyCrossing D := by
  by_cases pairs : ∀ i j, i ≠ j → Cross (D i) (D j)
  · exact flower_uniform D k (CubicalDiagrams.P118.flower_of_large_corner_cover D q k
      unbreakable orders (large_corner_cover D q k equity criss pairs))
  · exact uniform_of_not_pairwise D k equity pairs

end CornerSection
