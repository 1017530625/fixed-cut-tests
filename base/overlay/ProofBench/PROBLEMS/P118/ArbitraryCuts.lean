import ProofBench.PROBLEMS.P118.CutRequirements
import ProofBench.PROBLEMS.P118.CubeTransversals
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Arbitrary fixed cut tests for the weighted three-cube corner lemma. -/

namespace CornerArbitraryCuts

open Finset CornerLemma CornerCutLowerBound
open CoverAware (ring index)

set_option maxRecDepth 25000
set_option maxHeartbeats 5000000
set_option synthInstance.maxSize 1024

private abbrev axis (i : Fin 3) : Finset Vertex := univ.filter fun v => v i = false
private abbrev cube : Face := fun _ => none
private abbrev crosses (A : Finset Vertex) (f : Face) :=
  ∃ u v, Adj u v ∧ u ∈ A ∧ v ∉ A ∧ InFace u f ∧ InFace v f

private def coeff (A : Finset Vertex) (f : Face) : ℕ := if crosses A f then 1 else 0
private def atoms (q : Fin 4) (f : Face) : ℕ := ∑ u ∈ ring q, coeff {u} f
private def axes (f : Face) : ℕ := ∑ i : Fin 3, coeff (axis i) f

/-- Incidences between one face and the singleton and coordinate cuts. A face
whose incidence bound is tight is the cube or has all its edges on the ring. -/
private theorem incidence : ∀ (q : Fin 4) (f : Face),
    atoms q f ≤ 2 * axes f ∧
    (atoms q f = 2 * axes f → f = cube ∨ ∀ u v, Adj u v →
      InFace u f → InFace v f → u ∈ ring q ∧ v ∈ ring q) := by decide

private theorem match_ring : ∀ (q : Fin 4) (b : Bool),
    (AlternatingMatching (index q b)).biUnion id = ring q := by decide
private theorem ring_size : ∀ q : Fin 4, (ring q).card = 6 := by decide
private theorem index_surj : ∀ j : Fin 8, ∃ (q : Fin 4) (b : Bool), index q b = j := by decide
private theorem reverse_adj : ∀ u v : Vertex, Adj u v → Adj v u := by decide
private theorem matching_crosses_cube : ∀ j : Fin 8, ∀ e ∈ AlternatingMatching j,
    crosses e cube := by decide

/-- A nontrivial union of parts of a three-edge matching is one matched edge
or the complement of one matched edge, when restricted to the six endpoints. -/
private theorem detected_pattern : ∀ (q : Fin 4) (b : Bool) (A : Finset Vertex),
    index q b ∈ detected A → ∃ e ∈ AlternatingMatching (index q b),
      (∀ u ∈ ring q, u ∈ A ↔ u ∈ e) ∨
      (∀ u ∈ ring q, u ∈ A ↔ u ∉ e) := by decide

private def corners (f : Face) : Finset Vertex := univ.filter fun u => InFace u f
private def witness (j : Fin 8) (f : Face) : ℕ := if corners f ∈ AlternatingMatching j then 1 else 0
private theorem matching_faces : ∀ j : Fin 8, ∀ e ∈ AlternatingMatching j,
    (∃ f, corners f = e) ∧ (∀ u ∈ e, ∀ v ∈ e, u ≠ v → Adj u v) := by decide
private theorem witness_coords : ∀ (j : Fin 8) (i : Fin 3),
    cutValue (witness j) (axis i) = 1 := by decide
private theorem witness_singles : ∀ (q : Fin 4) (b : Bool), ∀ u ∈ ring q,
    1 ≤ cutValue (witness (index q b)) {u} := by decide
private theorem witness_cube : ∀ j : Fin 8, witness j cube = 0 := by decide

private theorem cube_of_split : ∀ A : Finset Vertex, A.Nonempty → (univ \ A).Nonempty →
    crosses A cube := by decide

set_option maxHeartbeats 300000

private theorem cut_as_sum (w : Face → ℕ) (A : Finset Vertex) :
    cutValue w A = ∑ f : Face, w f * coeff A f := by
  unfold cutValue
  rw [sum_filter]
  apply sum_congr rfl
  intro f _
  by_cases h : crosses A f
  · simp [coeff, h]
  · simp [coeff, h]

private theorem sum_atoms (q : Fin 4) (w : Face → ℕ) :
    (∑ f : Face, w f * atoms q f) = ∑ u ∈ ring q, cutValue w {u} := by
  simp only [atoms, Finset.mul_sum, cut_as_sum]
  rw [sum_comm]

private theorem sum_axes (w : Face → ℕ) :
    (∑ f : Face, w f * (2 * axes f)) = 2 * ∑ i : Fin 3, cutValue w (axis i) := by
  have flip : (∑ f : Face, w f * axes f) = ∑ i : Fin 3, cutValue w (axis i) := by
    simp only [axes, Finset.mul_sum, cut_as_sum]
    rw [sum_comm]
  calc
    _ = ∑ f : Face, 2 * (w f * axes f) := sum_congr rfl fun _ _ => by ac_rfl
    _ = 2 * ∑ f : Face, w f * axes f := (Finset.mul_sum ..).symm
    _ = _ := congrArg (fun n : ℕ => 2 * n) flip

/-- Double-count the singleton and coordinate incidences. Equality of the
weighted totals forces equality on every face of positive weight. -/
private theorem support (q : Fin 4) (w : Face → ℕ) (k : ℕ)
    (coord : ∀ i, cutValue w (axis i) = k)
    (single : ∀ u ∈ ring q, k ≤ cutValue w {u}) (f : Face) (hf : w f ≠ 0) :
    f = cube ∨ ∀ u v, Adj u v → InFace u f → InFace v f → u ∈ ring q ∧ v ∈ ring q := by
  have scaled (g : Face) (_ : g ∈ (univ : Finset Face)) :
      w g * atoms q g ≤ w g * (2 * axes g) :=
    Nat.mul_le_mul_left _ (incidence q g).1
  have lower : 6 * k ≤ ∑ f : Face, w f * atoms q f := by
    rw [sum_atoms]
    calc
      6 * k = ∑ u ∈ ring q, k := by simp [ring_size]
      _ ≤ _ := sum_le_sum single
  have upper : (∑ f : Face, w f * (2 * axes f)) = 6 * k := by
    rw [sum_axes]
    simp [coord, ← Nat.mul_assoc]
  have eq := (sum_eq_sum_iff_of_le scaled).mp
    (le_antisymm (sum_le_sum scaled) (upper.le.trans lower))
  exact (incidence q f).2 (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hf) (eq f (mem_univ f)))

private abbrev pattern (R A B : Finset Vertex) :=
  (∀ u ∈ R, u ∈ A ↔ u ∈ B) ∨ (∀ u ∈ R, u ∈ A ↔ u ∉ B)

private theorem pattern_symm {R A B : Finset Vertex} (h : pattern R A B) : pattern R B A := by
  rcases h with h | h
  · exact Or.inl fun u hu => (h u hu).symm
  · right
    intro u hu
    refine ⟨fun hb ha => (h u hu).mp ha hb, fun ha => ?_⟩
    by_contra hb
    exact ha ((h u hu).mpr hb)

private theorem transfer {R A B : Finset Vertex} {f : Face}
    (h : pattern R A B)
    (inside : ∀ u v, Adj u v → InFace u f → InFace v f → u ∈ R ∧ v ∈ R)
    (cross : crosses A f) : crosses B f := by
  obtain ⟨u,v,adj,ua,va,uf,vf⟩ := cross
  obtain ⟨ur,vr⟩ := inside u v adj uf vf
  rcases h with h | h
  · exact ⟨u,v,adj,(h u ur).mp ua, fun vb => va ((h v vr).mpr vb),uf,vf⟩
  · have vb : v ∈ B := by
      by_contra h'
      exact va ((h v vr).mpr h')
    exact ⟨v,u,reverse_adj _ _ adj,vb,(h u ur).mp ua,vf,uf⟩

private theorem sides (q : Fin 4) (b : Bool) {A : Finset Vertex} (h : index q b ∈ detected A) :
    (∃ u ∈ ring q, u ∈ A) ∧ ∃ u ∈ ring q, u ∉ A := by
  have guard := (mem_filter.mp h).2
  dsimp only at guard
  rw [match_ring] at guard
  obtain ⟨⟨u,hu⟩,⟨v,hv⟩,_⟩ := guard
  exact ⟨⟨u,(mem_inter.mp hu).1,(mem_inter.mp hu).2⟩,v,(mem_sdiff.mp hv).1,(mem_sdiff.mp hv).2⟩

/-- On a ring satisfying the coordinate and singleton hypotheses, a cut that
detects a matching has exactly the value of one of that matching's edges.
The two corners outside the ring may be assigned to either side. -/
theorem cut_eq_matching_edge (q : Fin 4) (b : Bool) (A : Finset Vertex)
    (detect : index q b ∈ detected A) (w : Face → ℕ) (k : ℕ)
    (coord : ∀ i : Fin 3, cutValue w (univ.filter fun v => v i = false) = k)
    (single : ∀ u ∈ ring q, k ≤ cutValue w {u}) :
    ∃ e ∈ AlternatingMatching (index q b), cutValue w A = cutValue w e := by
  obtain ⟨e,he,h⟩ := detected_pattern q b A detect
  obtain ⟨⟨u,_,hu⟩,v,_,hv⟩ := sides q b detect
  have fullA := cube_of_split A ⟨u,hu⟩ ⟨v,mem_sdiff.mpr ⟨mem_univ _,hv⟩⟩
  refine ⟨e,he,?_⟩
  rw [cut_as_sum, cut_as_sum]
  apply sum_congr rfl
  intro f _
  by_cases zero : w f = 0
  · simp [zero]
  · have equiv : crosses A f ↔ crosses e f := by
      rcases support q w k coord single f zero with rfl | inside
      · exact ⟨fun _ => matching_crosses_cube _ e he, fun _ => fullA⟩
      · exact ⟨transfer h inside, transfer (pattern_symm h) inside⟩
    simp [coeff, equiv]

private theorem witness_not_flower (j : Fin 8) : ¬ IsFlower (witness j) 1 := by
  rintro ⟨_,_,l,small,full,_⟩
  change witness j cube = 1 - 2 * l at full
  rw [witness_cube] at full
  omega

private theorem witness_test (q : Fin 4) (b : Bool) (A : Finset Vertex)
    (miss : index q b ∉ detected A)
    (left : ∃ u ∈ ring q, u ∈ A) (right : ∃ u ∈ ring q, u ∉ A) :
    1 ≤ cutValue (witness (index q b)) A := by
  have split : ¬ ∀ e ∈ AlternatingMatching (index q b), e ⊆ A ∨ Disjoint e A := by
    intro none
    apply miss
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    dsimp only
    rw [match_ring]
    obtain ⟨u,ur,ua⟩ := left
    obtain ⟨v,vr,va⟩ := right
    exact ⟨⟨u,mem_inter.mpr ⟨ur,ua⟩⟩,⟨v,mem_sdiff.mpr ⟨vr,va⟩⟩,none⟩
  obtain ⟨e,edgeSplit⟩ := not_forall.mp split
  have he : e ∈ AlternatingMatching (index q b) := by
    by_contra absent
    exact edgeSplit fun h => (absent h).elim
  obtain ⟨notSubset,notDisjoint⟩ := not_or.mp (fun choice => edgeSplit (fun _ => choice))
  obtain ⟨u,ue,ua⟩ := Finset.not_disjoint_iff.mp notDisjoint
  obtain ⟨v,ve,va⟩ := Finset.not_subset.mp notSubset
  obtain ⟨⟨f,face⟩,adj⟩ := matching_faces (index q b) e he
  have inFace (x : Vertex) (hx : x ∈ e) : InFace x f := (mem_filter.mp (face ▸ hx : x ∈ corners f)).2
  have cut : crosses A f :=
    ⟨u,v,adj u ue v ve (fun eq => va (eq ▸ ua)),ua,va,inFace u ue,inFace v ve⟩
  calc
    1 = witness (index q b) f := by simp [witness, face, he]
    _ ≤ cutValue _ A := Finset.single_le_sum (fun g _ => Nat.zero_le (witness _ g))
      (mem_filter.mpr ⟨mem_univ _,cut⟩)

/-- With the cover fixed to a six-cycle, arbitrary tests suffice exactly when
they detect its two alternating matchings. -/
theorem ring_sufficient_iff_complete (q : Fin 4) (S : Finset (Finset Vertex)) :
    CoverAware.SufficientAt (ring q) S ↔ ∀ b : Bool, ∃ A ∈ S, index q b ∈ detected A := by
  constructor
  · intro works b
    by_contra absent
    apply witness_not_flower (index q b)
    apply works (witness (index q b)) 1 (witness_coords _) (witness_singles q b)
    intro A ha
    exact witness_test q b A (fun h => absent ⟨A,ha,h⟩)
  · intro complete w k coord single tests
    let good : Finset (Finset Vertex) := univ.filter (fun e => k ≤ cutValue w e)
    apply CoverAware.ring_sufficient_of_hits q good ?_ w k coord single ?_
    · intro b
      obtain ⟨A,ha,d⟩ := complete b
      obtain ⟨e,he,eq⟩ := cut_eq_matching_edge q b A d w k coord single
      obtain ⟨left,right⟩ := sides q b d
      exact ⟨e,he,mem_filter.mpr ⟨mem_univ _, eq ▸ tests A ha left right⟩⟩
    · intro A ha _ _
      exact (mem_filter.mp ha).2

/-- A family of vertex subsets works for all thresholds, natural face weights
and vertex covers exactly when it detects all eight alternating matchings. -/
theorem sufficient_iff_complete (S : Finset (Finset Vertex)) :
    CubeTransversals.Sufficient S ↔ Complete S := by
  constructor
  · intro works j
    obtain ⟨q,b,rfl⟩ := index_surj j
    apply (ring_sufficient_iff_complete q S).mp _ b
    intro w k coord single tests
    exact works w k (ring q) coord (CoverAware.ring_is_cover q) single tests
  · intro complete w k R coord cover single tests
    rcases CoverAware.cover_classification R cover with ⟨p,hp⟩ | ⟨q,rfl⟩
    · exact CoverAware.parity_sufficient p hp S w k coord single tests
    · exact ((ring_sufficient_iff_complete q S).mpr (fun b => complete (index q b)))
        w k coord single tests

end CornerArbitraryCuts

#print axioms CornerArbitraryCuts.cut_eq_matching_edge
#print axioms CornerArbitraryCuts.ring_sufficient_iff_complete
#print axioms CornerArbitraryCuts.sufficient_iff_complete
