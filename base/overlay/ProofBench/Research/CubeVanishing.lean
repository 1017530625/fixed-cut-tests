import ProofBench.Research.CubicalP118
import ProofBench.PROBLEMS.P118.CoverAware
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Weighted faces of the three-cube and vertex covers. See Bourneuf et al.,
Section 4.1, Lemmas 4.1–4.7. -/
namespace CubeVanishing

open Finset CornerLemma

abbrev axisSide (i : Fin 3) : Finset Vertex := univ.filter fun u => u i = false
abbrev IsCornerMap (w : Face → ℕ) (k : ℕ) := ∀ i, cutValue w (axisSide i) = k
abbrev opposite (u : Vertex) : Vertex := fun i => !(u i)
/-- The edge and the two square faces through adjacent vertices. -/
abbrev onEdge (u v : Vertex) (f : Face) : Prop :=
  (dim f = 1 ∨ dim f = 2) ∧ InFace u f ∧ InFace v f

private inductive Test where
  | axis (i : Fin 3)
  | atomic (u : Vertex)
  | pair (u v : Vertex)
  deriving DecidableEq

private def Test.side : Test → Finset Vertex
  | .axis i => axisSide i
  | .atomic u => {u}
  | .pair u v => {u,v}

private def Test.coeff : Test → Face → ℕ
  | .axis i, f => if f i = none then 1 else 0
  | .atomic u, f => if 0 < dim f ∧ InFace u f then 1 else 0
  | .pair u v, f =>
    if (InFace u f ∨ InFace v f) ∧
      (1 < dim f ∨ (dim f = 1 ∧ ¬(u ≠ v ∧ InFace u f ∧ InFace v f))) then 1 else 0

private abbrev meetsBoth (A : Finset Vertex) (f : Face) : Prop :=
  (∃ u ∈ A, InFace u f) ∧ ∃ v ∈ univ \ A, InFace v f

set_option maxRecDepth 16000
set_option synthInstance.maxSize 1024

private theorem coeff_correct (t : Test) (f : Face) :
    (if meetsBoth t.side f then 1 else 0) = t.coeff f := by
  cases t with
  | axis i => revert i f; decide
  | atomic u => revert u f; decide
  | pair u v => revert u v f; decide

private theorem sum_one (w : Face → ℕ) (t : Test) :
    (∑ f : Face, w f * t.coeff f) = cutValue w t.side := by
  rw [← CubicalDiagrams.P118.cutValue_eq, CubicalDiagrams.cutValue_eq_sum]
  apply sum_congr rfl
  intro f _
  rw [← coeff_correct]
  by_cases h : meetsBoth t.side f
  · have hm := (CubicalDiagrams.mem_crossingFaces_iff t.side f).2 h
    rw [ite_eq_left h, ite_eq_left hm, Nat.mul_one]
  · have hm := mt (CubicalDiagrams.mem_crossingFaces_iff t.side f).1 h
    rw [ite_eq_right h, ite_eq_right hm, Nat.mul_zero]

private def coeffSum (L : List Test) (f : Face) : ℕ := (L.map fun t => t.coeff f).sum

private theorem weighted (w : Face → ℕ) (L : List Test) :
    (∑ f : Face, w f * coeffSum L f) = (L.map fun t => cutValue w t.side).sum := by
  induction L with
  | nil => simp [coeffSum]
  | cons t L ih =>
    simp only [coeffSum, List.map_cons, List.sum_cons, Nat.mul_add, sum_add_distrib] at ih ⊢
    rw [sum_one, ih]

private theorem sum_of_constant (w : Face → ℕ) (L : List Test) (k : ℕ)
    (h : ∀ t ∈ L, cutValue w t.side = k) :
    (L.map fun t => cutValue w t.side).sum = L.length * k := by
  induction L with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    rw [h a (by simp), ih (fun t ht => h t (by simp [ht]))]
    omega

private theorem strict_forces_zero (w low high : Face → ℕ)
    (ordered : ∀ f, w f ≠ 0 → low f ≤ high f)
    (total : (∑ f : Face, w f * high f) ≤ ∑ f : Face, w f * low f)
    (f : Face) (strict : low f < high f) : w f = 0 := by
  by_contra nz
  have point (g : Face) (_ : g ∈ (univ : Finset Face)) : w g * low g ≤ w g * high g := by
    by_cases z : w g = 0
    · simp [z]
    · exact Nat.mul_le_mul_left _ (ordered _ z)
  have allEq := (sum_eq_sum_iff_of_le point).mp (le_antisymm (sum_le_sum point) total)
  exact (Nat.ne_of_lt strict)
    (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero nz) (allEq f (mem_univ f)))

private def flipAt (u : Vertex) (i : Fin 3) : Vertex := fun j => if i = j then !(u j) else u j

/-- Four edge sides meeting the given edge in exactly one vertex. -/
private def near (u v : Vertex) : List Test :=
  (List.finRange 3).flatMap fun i => if u i = v i then
    [.pair u (flipAt u i), .pair v (flipAt v i)] else []

/-- The coordinate perpendicular to the cut containing the given edge is counted twice. -/
private def twice (u v : Vertex) : List Test :=
  (List.finRange 3).flatMap fun i => if u i = v i then [.axis i] else [.axis i,.axis i]

abbrev MeetsExactlyOne (A : Finset Vertex) (u v : Vertex) : Prop :=
  (u ∈ A ∧ v ∉ A) ∨ (v ∈ A ∧ u ∉ A)

private def Test.validNear (u v : Vertex) : Test → Prop
  | .pair a b => Adj a b ∧ MeetsExactlyOne {a,b} u v
  | _ => False

private instance (u v : Vertex) (t : Test) : Decidable (t.validNear u v) := by
  cases t <;> unfold Test.validNear <;> infer_instance

private def Test.isAxis : Test → Bool
  | .axis _ => true
  | _ => false

set_option maxHeartbeats 4500000 in
private theorem edge_tests : ∀ u v : Vertex, Adj u v →
    (near u v).length = 4 ∧ (twice u v).length = 4 ∧
    (∀ t ∈ near u v, t.validNear u v) ∧
    (∀ t ∈ twice u v, t.isAxis = true) := by decide

set_option maxHeartbeats 4500000 in
private theorem opposite_incidence : ∀ u v : Vertex, Adj u v → ∀ f : Face,
    (¬onEdge u v f → coeffSum (near u v) f ≤ coeffSum (twice u v) f) ∧
    (onEdge (opposite u) (opposite v) f → coeffSum (near u v) f < coeffSum (twice u v) f) := by
  decide

/-- Lemma 4.6. Vanishing on an edge and its incident squares propagates
to the opposite edge and its incident squares when the four local pair cuts are tight. -/
theorem opposite_edge_vanishes (w : Face → ℕ) (k : ℕ) (coord : IsCornerMap w k)
    (u v : Vertex) (adj : Adj u v) (zero : ∀ f, onEdge u v f → w f = 0)
    (tight : ∀ a b : Vertex, Adj a b → MeetsExactlyOne {a,b} u v → cutValue w {a,b} = k)
    (f : Face) (face : onEdge (opposite u) (opposite v) f) : w f = 0 := by
  obtain ⟨n, m, nearSpec, coordSpec⟩ := edge_tests u v adj
  apply strict_forces_zero w (coeffSum (near u v)) (coeffSum (twice u v))
  · intro g positive
    exact (opposite_incidence u v adj g).1 (fun on => positive (zero _ on))
  · rw [weighted, weighted]
    have sides : ∀ t ∈ near u v, cutValue w t.side = k := by
      intro t ht
      have h := nearSpec t ht
      cases t with
      | axis i => exact False.elim h
      | atomic a => exact False.elim h
      | pair a b => exact tight _ _ h.1 h.2
    have axes : ∀ t ∈ twice u v, cutValue w t.side = k := by
      intro t ht
      have h := coordSpec t ht
      cases t with
      | axis i => exact coord i
      | atomic a => contradiction
      | pair a b => contradiction
    rw [sum_of_constant _ _ k sides, sum_of_constant _ _ k axes, n, m]
  · exact (opposite_incidence u v adj f).2 face

private def atoms (u v : Vertex) : List Test := [.atomic u, .atomic v]
private def pairs (u v b : Vertex) : List Test := [.pair u b, .pair v b]

set_option maxHeartbeats 4500000 in
private theorem wedge_incidence : ∀ b u : Vertex, Adj b u → ∀ v : Vertex, Adj b v →
    u ≠ v → ∀ x : Vertex, Adj b x → x ≠ u → x ≠ v → ∀ f : Face,
    coeffSum (atoms u v) f ≤ coeffSum (pairs u v b) f ∧
    (onEdge b x f → coeffSum (atoms u v) f < coeffSum (pairs u v b) f) := by decide

/-- Lemma 4.7. For a wedge with two distinct ends, the two singleton
lower bounds and two pair upper bounds force vanishing on the third incident edge.
The argument also applies without any hypotheses on the three coordinate cuts. -/
theorem third_edge_vanishes (w : Face → ℕ) (k : ℕ) (u v b x : Vertex)
    (ub : Adj b u) (vb : Adj b v) (different : u ≠ v)
    (xb : Adj b x) (xu : x ≠ u) (xv : x ≠ v)
    (loU : k ≤ cutValue w {u}) (loV : k ≤ cutValue w {v})
    (hiU : cutValue w {u,b} ≤ k) (hiV : cutValue w {v,b} ≤ k)
    (f : Face) (face : onEdge b x f) : w f = 0 := by
  apply strict_forces_zero w (coeffSum (atoms u v)) (coeffSum (pairs u v b))
  · intro g _
    exact (wedge_incidence b u ub v vb different x xb xu xv g).1
  · rw [weighted, weighted]
    simp only [pairs, atoms, Test.side, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    omega
  · exact (wedge_incidence b u ub v vb different x xb xu xv f).2 face

alias lemma4_6 := opposite_edge_vanishes

abbrev distance (u v : Vertex) : ℕ := (univ.filter fun i => u i ≠ v i).card

/-- The paper's distance-two formulation of Lemma 4.7. -/
theorem lemma4_7 (w : Face → ℕ) (k : ℕ) (_coord : IsCornerMap w k) (u v b x : Vertex)
    (distanceTwo : distance u v = 2) (ub : Adj b u) (vb : Adj b v)
    (xb : Adj b x) (xu : x ≠ u) (xv : x ≠ v)
    (loU : k ≤ cutValue w {u}) (loV : k ≤ cutValue w {v})
    (hiU : cutValue w {u,b} ≤ k) (hiV : cutValue w {v,b} ≤ k)
    (f : Face) (face : onEdge b x f) : w f = 0 := by
  have diff : u ≠ v := by
    rintro rfl
    simp [distance] at distanceTwo
  exact third_edge_vanishes w k u v b x ub vb diff xb xu xv loU loV hiU hiV f face


/-- Every edge of the ordinary cube has an endpoint in R. -/
abbrev VertexCover (R : Finset Vertex) : Prop :=
  ∀ u v : Vertex, Adj u v → u ∈ R ∨ v ∈ R

abbrev Independent (R : Finset Vertex) : Prop :=
  ∀ u ∈ R, ∀ v ∈ R, ¬ Adj u v

/-- The paper defines an anti-diagonal six-cycle by its two missing antipodes.
The six-cycle property of this set is certified by `antiDiagonal_induces_cycle`. -/
abbrev AntiDiagonalCycle (R : Finset Vertex) : Prop :=
  ∃ p : Vertex, R = univ \ {p, opposite p}

private def cycleVertex (p : Vertex) (j : Fin 6) : Vertex := fun i =>
  (p i).xor (match i.val with
    | 0 => decide (3 ≤ j.val)
    | 1 => decide (1 ≤ j.val ∧ j.val ≤ 3)
    | _ => decide (j.val = 0 ∨ j.val = 1 ∨ j.val = 5))

private theorem cycleModel : ∀ p : Vertex,
    (∀ u : Vertex, u ∈ univ \ {p, opposite p} ↔ ∃ j, cycleVertex p j = u) ∧
    Function.Injective (cycleVertex p) ∧
    ∀ i j : Fin 6, Adj (cycleVertex p i) (cycleVertex p j) ↔
      i + 1 = j ∨ j + 1 = i := by decide

theorem antiDiagonal_induces_cycle (R : Finset Vertex) (h : AntiDiagonalCycle R) :
    ∃ c : Fin 6 → Vertex, (∀ u, u ∈ R ↔ ∃ i, c i = u) ∧ Function.Injective c ∧
      ∀ i j, Adj (c i) (c j) ↔ i + 1 = j ∨ j + 1 = i := by
  obtain ⟨p,rfl⟩ := h
  exact ⟨cycleVertex p, cycleModel p⟩

private theorem independent_four_parity : ∀ I : Finset Vertex,
    I.card = 4 → Independent I → ∃ p, I = CoverAware.parityClass p := by decide

private theorem parity_properties : ∀ p : Bool,
    (CoverAware.parityClass p).card = 4 ∧ Independent (CoverAware.parityClass p) ∧
    VertexCover (CoverAware.parityClass p) := by decide

private theorem antipodes_ring : ∀ p : Vertex, ∃ q : Fin 4,
    univ \ {p, opposite p} = CoverAware.ring q := by decide

/-- Lemma 4.2, including the converse for any chosen independent four-set. -/
theorem lemma4_2 (R : Finset Vertex) :
    VertexCover R ↔
    (∃ I : Finset Vertex, I ⊆ R ∧ I.card = 4 ∧ Independent I) ∨ AntiDiagonalCycle R := by
  constructor
  · intro cover
    rcases CoverAware.cover_classification R cover with ⟨p,hp⟩ | ⟨q,rfl⟩
    · exact Or.inl ⟨_, hp, (parity_properties p).1, (parity_properties p).2.1⟩
    · exact Or.inr (CoverAware.ring_is_antidiagonal q)
  · rintro (⟨I,sub,card,indep⟩ | ⟨p,rfl⟩)
    · obtain ⟨p,rfl⟩ := independent_four_parity I card indep
      intro u v adj
      exact ((parity_properties p).2.2 u v adj).imp (fun h => sub h) (fun h => sub h)
    · obtain ⟨q,hq⟩ := antipodes_ring p
      rw [hq]
      exact CoverAware.ring_is_cover q

/-- The sum of the face weights in dimension `d`, denoted s(d) in the paper. -/
def faceMass (w : Face → ℕ) (d : ℕ) : ℕ :=
  ∑ f ∈ univ.filter (fun f : Face => dim f = d), w f

private def mark (d : ℕ) (f : Face) : ℕ := if dim f = d then 1 else 0

private theorem sum_mark (w : Face → ℕ) (d : ℕ) :
    (∑ f : Face, w f * mark d f) = faceMass w d := by
  rw [faceMass, sum_filter]
  apply sum_congr rfl
  intro f _
  by_cases h : dim f = d <;> simp [mark, h]

private theorem split_sums (w : Face → ℕ) (a b c : ℕ) :
    (∑ f : Face, w f * (mark 3 f * a + mark 2 f * b + mark 1 f * c)) =
      faceMass w 3 * a + faceMass w 2 * b + faceMass w 1 * c := by
  simp only [Nat.mul_add, ← Nat.mul_assoc, sum_add_distrib, ← sum_mul, sum_mark]

private def axes : List Test := [.axis 0, .axis 1, .axis 2]

private theorem axes_coeff : ∀ f : Face,
    coeffSum axes f = mark 3 f * 3 + mark 2 f * 2 + mark 1 f * 1 := by decide

/-- Lemma 4.3. A face occurs in exactly as many coordinate cuts as its dimension. -/
theorem lemma4_3 (w : Face → ℕ) (k : ℕ) (coord : IsCornerMap w k) :
    3 * faceMass w 3 + 2 * faceMass w 2 + faceMass w 1 = 3 * k := by
  have h := weighted w axes
  simp_rw [axes_coeff] at h
  rw [split_sums] at h
  simp [axes, Test.side, coord] at h
  omega

private def parityCoeff (p : Bool) (f : Face) :=
  ∑ u ∈ CoverAware.parityClass p, (Test.atomic u).coeff f

private theorem parity_coeff : ∀ (p : Bool) (f : Face),
    parityCoeff p f = mark 3 f * 4 + mark 2 f * 2 + mark 1 f * 1 := by decide

private theorem atomic_identity (w : Face → ℕ) (p : Bool) :
    (∑ u ∈ CoverAware.parityClass p, cutValue w {u}) =
      faceMass w 3 * 4 + faceMass w 2 * 2 + faceMass w 1 * 1 := by
  calc
    _ = ∑ f : Face, w f * parityCoeff p f := by
      simp only [parityCoeff, Finset.mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro u _
      exact (sum_one w (.atomic u)).symm
    _ = _ := by simp_rw [parity_coeff]; apply split_sums

private theorem mass_full (w : Face → ℕ) : faceMass w 3 = w (fun _ => none) := by
  have top : univ.filter (fun f : Face => dim f = 3) = {fun _ => none} := by decide
  simp [faceMass, top]

private theorem le_mass (w : Face → ℕ) (f : Face) (d : ℕ) (hf : dim f = d) :
    w f ≤ faceMass w d :=
  single_le_sum (f := w) (fun _ _ => Nat.zero_le _) (mem_filter.mpr ⟨mem_univ _, hf⟩)

private theorem full_le_coord (w : Face → ℕ) (k : ℕ) (coord : IsCornerMap w k) :
    faceMass w 3 ≤ k := by
  rw [mass_full, ← coord 0]
  change w (fun _ => none) ≤ cutValue w (Test.axis 0).side
  rw [← sum_one]
  have h := single_le_sum (s := (univ : Finset Face))
    (f := fun f => w f * (Test.axis 0).coeff f) (fun _ _ => Nat.zero_le _)
    (mem_univ (fun _ => none : Face))
  simpa only [Test.coeff, ite_true, Nat.mul_one] using h

/-- Lemma 4.4, with the stronger conclusion identified in its proof:
the cube has weight k, and every edge and square has weight zero. -/
theorem lemma4_4 (w : Face → ℕ) (k : ℕ) (coord : IsCornerMap w k)
    (R : Finset Vertex) (card : R.card = 4) (indep : Independent R)
    (lower : ∀ u ∈ R, k ≤ cutValue w {u}) :
    w (fun _ => none) = k ∧ (∀ f, dim f = 1 ∨ dim f = 2 → w f = 0) ∧ IsFlower w k := by
  obtain ⟨p,rfl⟩ := independent_four_parity R card indep
  have h₁ := lemma4_3 w k coord
  have h₂ := sum_le_sum lower
  simp only [sum_const, card, nsmul_eq_mul, atomic_identity] at h₂
  have h₃ := full_le_coord w k coord
  have hfull : w (fun _ => none) = k := by rw [← mass_full w]; omega
  have vanish : ∀ f, dim f = 1 ∨ dim f = 2 → w f = 0 := by
    intro f dimF
    rcases dimF with edge | square
    · have h := le_mass w f 1 edge
      omega
    · have h := le_mass w f 2 square
      omega
  refine ⟨hfull, vanish, fun f h => vanish f (Or.inr h), (fun _ => false), 0, by simp, ?_, ?_⟩
  · simpa using hfull
  · intro f edge
    simpa using vanish f (Or.inl edge)

abbrev Crosses (R A : Finset Vertex) : Prop :=
  (∃ u ∈ R, u ∈ A) ∧ ∃ v ∈ R, v ∉ A

private theorem ring_other : ∀ (q : Fin 4) (u : Vertex), ∃ v ∈ CoverAware.ring q, v ≠ u := by
  decide

private theorem all_hits : ∀ q : Fin 4, CoverAware.HitsAt q univ := by
  unfold CoverAware.HitsAt
  decide

/-- Lemma 4.5, with every R-crossing cut available in its hypotheses. -/
theorem lemma4_5 (w : Face → ℕ) (k : ℕ) (coord : IsCornerMap w k)
    (R : Finset Vertex) (cycle : AntiDiagonalCycle R)
    (lower : ∀ A, Crosses R A → k ≤ cutValue w A) : IsFlower w k := by
  obtain ⟨p,rfl⟩ := cycle
  obtain ⟨q,hq⟩ := antipodes_ring p
  rw [hq] at lower
  apply CoverAware.ring_sufficient_of_hits q univ (all_hits q) w k coord
  · intro u hu
    obtain ⟨v,hv,ne⟩ := ring_other q u
    exact lower {u} ⟨⟨u,hu, mem_singleton_self u⟩, v, hv, fun h => ne (mem_singleton.mp h)⟩
  · intro A _ left right
    exact lower A ⟨left,right⟩

private theorem other_parity_vertex : ∀ (p : Bool) (u : Vertex),
    ∃ v ∈ CoverAware.parityClass p, v ≠ u := by decide

/-- Lemma 4.1 from the two vertex-cover cases of Lemma 4.2. -/
theorem lemma4_1 (w : Face → ℕ) (k : ℕ) (coord : IsCornerMap w k)
    (R : Finset Vertex) (cover : VertexCover R)
    (lower : ∀ A, Crosses R A → k ≤ cutValue w A) : IsFlower w k := by
  rcases (lemma4_2 R).1 cover with ⟨I,sub,card,indep⟩ | cycle
  · obtain ⟨p,rfl⟩ := independent_four_parity I card indep
    apply (lemma4_4 w k coord _ card indep ?_).2.2
    intro u hu
    obtain ⟨v,hv,ne⟩ := other_parity_vertex p u
    exact lower {u} ⟨⟨u,sub hu,mem_singleton_self u⟩, v,sub hv,fun h => ne (mem_singleton.mp h)⟩
  · exact lemma4_5 w k coord R cycle lower

/-- The LPBench representation assigns weights even to vertices. Agreement on
positive-dimensional faces already determines the value of every cut. -/
theorem cutValue_congr_of_positive (w₁ w₂ : Face → ℕ)
    (agree : ∀ f, 0 < dim f → w₁ f = w₂ f) (A : Finset Vertex) :
    cutValue w₁ A = cutValue w₂ A := by
  have dimension : ∀ (u v : Vertex), Adj u v → ∀ f : Face, InFace u f → InFace v f → 0 < dim f := by
    decide
  unfold cutValue
  apply sum_congr rfl
  intro f hf
  obtain ⟨u,v,adj,_,_,hu,hv⟩ := (mem_filter.mp hf).2
  exact agree f (dimension u v adj f hu hv)

end CubeVanishing
