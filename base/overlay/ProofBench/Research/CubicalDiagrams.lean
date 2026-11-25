import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Separation

/-!
# Cubical diagrams of finite graph separations

An indexed family of oriented vertex separations sends each graph vertex to
a face of the Boolean cube. A partition of the corners lifts to a graph
separation. Its order counts the face weights incident with an actual cut
edge. The coordinate type is finite and may be empty.
-/

namespace CubicalDiagrams

open Finset

universe u
variable {I : Type u}

/-- A full assignment of Boolean coordinates. -/
abbrev Corner (I : Type*) := I → Bool

/-- A partial assignment. A missing bit is a free coordinate. -/
abbrev Face (I : Type*) := I → Option Bool

/-- A corner extends all fixed bits of the face. -/
abbrev InFace (p : Corner I) (f : Face I) : Prop :=
  ∀ i, f i = none ∨ f i = some (p i)

/-- Complete a face using the given bit at its free coordinates. -/
def fill (f : Face I) (b : Bool) : Corner I := fun i => (f i).getD b

theorem fill_inFace (f : Face I) (b : Bool) : InFace (fill f b) f := by
  intro i
  cases h : f i <;> simp [fill, h]

variable [Fintype I]

/-- Coordinates at which two corners disagree. -/
def differences (p q : Corner I) : Finset I := univ.filter fun i => p i ≠ q i

/-- Adjacency is Hamming distance one. -/
abbrev Adj (p q : Corner I) : Prop := (differences p q).card = 1

/-- The graph of corners and single-coordinate changes. -/
def cubeGraph (I : Type*) [Fintype I] : SimpleGraph (Corner I) where
  Adj := Adj
  symm := ⟨fun p q h => by
    have he : differences q p = differences p q := by
      ext i
      simp [differences, ne_comm]
    change (differences q p).card = 1
    rwa [he]⟩
  loopless := ⟨fun p => by simp [Adj, differences]⟩

/-- The cube graph induced on the corners of a face. -/
abbrev faceGraph (f : Face I) := (cubeGraph I).induce {p | InFace p f}

variable [DecidableEq I]

/-- Any two corners of the same face can be joined inside it by a walk
whose length equals the number of differing coordinates. -/
theorem exists_face_walk (f : Face I) (p q : {v : Corner I // InFace v f}) :
    ∃ walk : (faceGraph f).Walk p q, walk.length = (differences p.val q.val).card := by
  by_cases he : p = q
  · subst q
    exact ⟨.nil, by simp [differences]⟩
  · have hd : ∃ i, p.val i ≠ q.val i := by
      by_contra! h
      exact he (Subtype.ext (funext h))
    obtain ⟨i, hi⟩ := hd
    let next := Function.update p.val i (q.val i)
    have inside : InFace next f := by
      intro j
      by_cases h : j = i
      · subst j
        simpa [next] using q.property i
      · simpa [next, h] using p.property j
    let r : {v : Corner I // InFace v f} := ⟨next, inside⟩
    have single : differences p.val r.val = {i} := by
      ext j
      by_cases h : j = i
      · subst j
        simp [differences, r, next, hi]
      · simp [differences, r, next, h]
    have erased : differences r.val q.val = (differences p.val q.val).erase i := by
      ext j
      by_cases h : j = i
      · subst j
        simp [differences, r, next]
      · simp [differences, r, next, h]
    have himem : i ∈ differences p.val q.val := mem_filter.mpr ⟨mem_univ _, hi⟩
    have edge : (faceGraph f).Adj p r := by
      change (differences p.val r.val).card = 1
      simp [single]
    obtain ⟨walk, length⟩ := exists_face_walk f r q
    refine ⟨.cons edge walk, ?_⟩
    rw [SimpleGraph.Walk.length_cons, length, erased]
    exact card_erase_add_one himem
termination_by (differences p.val q.val).card
decreasing_by
  rw [erased]
  exact card_erase_lt_of_mem himem

/-- Every face induces a connected graph, including a zero-dimensional face. -/
theorem face_connected (f : Face I) : (faceGraph f).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨fill f false, fill_inFace f false⟩, ?_⟩
  intro q
  obtain ⟨walk, _⟩ := exists_face_walk f ⟨_, fill_inFace f false⟩ q
  exact walk.reachable

/-- Faces containing both ends of a cube edge from the corner set to its complement. -/
def crossingFaces (A : Finset (Corner I)) : Finset (Face I) :=
  univ.filter fun f => ∃ p q, Adj p q ∧ p ∈ A ∧ q ∉ A ∧ InFace p f ∧ InFace q f

/-- Testing whether a face meets both sides is equivalent to testing actual edges. -/
theorem mem_crossingFaces_iff (A : Finset (Corner I)) (f : Face I) :
    f ∈ crossingFaces A ↔ (∃ p ∈ A, InFace p f) ∧ ∃ q ∈ univ \ A, InFace q f := by
  simp only [crossingFaces, mem_filter, mem_univ, true_and, mem_sdiff]
  constructor
  · rintro ⟨p, q, _, hp, hq, fp, fq⟩
    exact ⟨⟨p, hp, fp⟩, q, hq, fq⟩
  · rintro ⟨⟨p, hp, fp⟩, q, hq, fq⟩
    obtain ⟨walk⟩ := (face_connected f) ⟨p, fp⟩ ⟨q, fq⟩
    obtain ⟨d, _, h₁, h₂⟩ := walk.exists_boundary_dart {v | v.val ∈ A} hp hq
    exact ⟨d.fst.val, d.snd.val, d.adj, h₁, h₂, d.fst.property, d.snd.property⟩

/-- The weight of the faces containing an edge of the cut. Each face is counted once. -/
def cutValue (w : Face I → ℕ) (A : Finset (Corner I)) : ℕ :=
  ∑ f ∈ crossingFaces A, w f

theorem crossingFaces_complement (A : Finset (Corner I)) :
    crossingFaces (univ \ A) = crossingFaces A := by
  have h : univ \ (univ \ A) = A := by ext p; simp
  ext f
  rw [mem_crossingFaces_iff, mem_crossingFaces_iff, h, and_comm]

theorem cutValue_complement (w : Face I → ℕ) (A : Finset (Corner I)) :
    cutValue w (univ \ A) = cutValue w A := by
  simp only [cutValue, crossingFaces_complement]

theorem cutValue_eq_sum (w : Face I → ℕ) (A : Finset (Corner I)) :
    cutValue w A = ∑ f, (if f ∈ crossingFaces A then w f else 0) := by
  rw [← sum_filter]
  simp [cutValue]

variable {X : Type*} [Fintype X] [DecidableEq X] {G : SimpleGraph X}

/-- The false and true bits index the first and second sides of a separation. -/
def side (s : G.Separation) (b : Bool) : Finset X := if b then s.B else s.A

private theorem belongs (s : G.Separation) (x : X) : x ∈ s.A ∨ x ∈ s.B := by
  apply mem_union.mp
  rw [s.union_eq]
  exact mem_univ x

/-- A graph vertex is free precisely at the separations whose separator contains it. -/
def faceOf (D : I → G.Separation) (x : X) : Face I := fun i =>
  if x ∈ (D i).A then (if x ∈ (D i).B then none else some false) else some true

/-- Number of graph vertices labelled by a given face. -/
def weight (D : I → G.Separation) (f : Face I) : ℕ :=
  (univ.filter fun x => faceOf D x = f).card

omit [Fintype I] [DecidableEq I] in
theorem agrees_iff (D : I → G.Separation) (x : X) (i : I) (b : Bool) :
    (faceOf D x i = none ∨ faceOf D x i = some b) ↔ x ∈ side (D i) b := by
  have h := belongs (D i) x
  cases b <;> by_cases ha : x ∈ (D i).A <;> by_cases hb : x ∈ (D i).B <;>
    simp_all [faceOf, side]

omit [Fintype I] [DecidableEq I] in
theorem inFace_iff (D : I → G.Separation) (p : Corner I) (x : X) :
    InFace p (faceOf D x) ↔ ∀ i, x ∈ side (D i) (p i) :=
  forall_congr' fun i => agrees_iff D x i (p i)

/-- Union of the inclusive corner regions picked out by a set of corners. -/
def aggregate (D : I → G.Separation) (A : Finset (Corner I)) : Finset X :=
  univ.filter fun x => ∃ p ∈ A, InFace p (faceOf D x)

omit [DecidableEq I] in
theorem mem_aggregate_iff (D : I → G.Separation) (A : Finset (Corner I)) (x : X) :
    x ∈ aggregate D A ↔ ∃ p ∈ A, ∀ i, x ∈ side (D i) (p i) := by
  simp [aggregate, inFace_iff]

private theorem share_side (s : G.Separation) {x y : X} (xy : G.Adj x y) :
    ∃ b : Bool, x ∈ side s b ∧ y ∈ side s b := by
  have hx := belongs s x
  have hy := belongs s y
  have noXY : x ∈ s.A ∧ x ∉ s.B → ¬(y ∈ s.B ∧ y ∉ s.A) := fun h g =>
    s.no_edge_across xy (mem_sdiff.mpr h) (mem_sdiff.mpr g)
  have noYX : y ∈ s.A ∧ y ∉ s.B → ¬(x ∈ s.B ∧ x ∉ s.A) := fun h g =>
    s.no_edge_across xy.symm (mem_sdiff.mpr h) (mem_sdiff.mpr g)
  by_cases h : x ∈ s.A ∧ y ∈ s.A
  · exact ⟨false, h⟩
  · refine ⟨true, ?_⟩
    change x ∈ s.B ∧ y ∈ s.B
    tauto

/-- The corner unions on the two sides of a cut form a graph separation. -/
def lift (D : I → G.Separation) (A : Finset (Corner I)) : G.Separation where
  A := aggregate D A
  B := aggregate D (univ \ A)
  union_eq := by
    apply eq_univ_of_forall
    intro x
    let p := fill (faceOf D x) false
    have hp := fill_inFace (faceOf D x) false
    by_cases h : p ∈ A
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, p, h, hp⟩)
    · exact mem_union_right _ (mem_filter.mpr
        ⟨mem_univ _, p, mem_sdiff.mpr ⟨mem_univ _, h⟩, hp⟩)
  no_edge_across := by
    intro x y xy hx hy
    choose p h using fun i => share_side (D i) xy
    by_cases hp : p ∈ A
    · exact (mem_sdiff.mp hy).2 ((mem_aggregate_iff D A y).mpr ⟨p, hp, fun i => (h i).2⟩)
    · exact (mem_sdiff.mp hx).2 ((mem_aggregate_iff D _ x).mpr
        ⟨p, mem_sdiff.mpr ⟨mem_univ _, hp⟩, fun i => (h i).1⟩)

/-- For every corner set, the lifted order is exactly the sum of the weights
of the faces containing a crossing edge. -/
theorem order_lift (D : I → G.Separation) (A : Finset (Corner I)) :
    (lift D A).order = cutValue (weight D) A := by
  have count : cutValue (weight D) A = (univ.filter fun x => faceOf D x ∈ crossingFaces A).card :=
    sum_card_fiberwise_eq_card_filter univ (crossingFaces A) (faceOf D)
  rw [count]
  apply congrArg Finset.card
  ext x
  change x ∈ aggregate D A ∩ aggregate D (univ \ A) ↔ _
  simp only [aggregate, mem_inter, mem_filter, mem_univ, true_and, mem_crossingFaces_iff]

/-- One of the two coordinate half-cubes. -/
def coordinateSide (i : I) (b : Bool) : Finset (Corner I) :=
  univ.filter fun p => p i = b

theorem complement_coordinateSide (i : I) (b : Bool) :
    univ \ coordinateSide i b = coordinateSide i (!b) := by
  ext p
  simp only [coordinateSide, mem_sdiff, mem_univ, mem_filter, true_and]
  cases b <;> cases p i <;> decide

/-- Aggregation recovers each inclusive side of each input separation. -/
theorem aggregate_coordinateSide (D : I → G.Separation) (i : I) (b : Bool) :
    aggregate D (coordinateSide i b) = side (D i) b := by
  ext x
  simp only [aggregate, coordinateSide, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, hf⟩
    simpa only [hp] using ((inFace_iff D p x).mp hf) i
  · intro hx
    refine ⟨fill (faceOf D x) b, ?_, fill_inFace _ _⟩
    rcases (agrees_iff D x i b).mpr hx with h | h <;> simp [fill, h]

/-- The complement of an individual corner aggregates the union of the
opposite inclusive coordinate sides. -/
theorem mem_aggregate_complement_singleton (D : I → G.Separation) (p : Corner I) (x : X) :
    x ∈ aggregate D (univ \ {p}) ↔ ∃ i, x ∈ side (D i) (!(p i)) := by
  rw [mem_aggregate_iff]
  simp only [mem_sdiff, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨q, hq, hs⟩
    have hd : ∃ i, q i ≠ p i := by
      by_contra! h
      exact hq (funext h)
    obtain ⟨i, hi⟩ := hd
    have flip : q i = !(p i) := by
      cases h₁ : q i <;> cases h₂ : p i <;> simp_all
    exact ⟨i, flip ▸ hs i⟩
  · rintro ⟨i, hx⟩
    rw [← aggregate_coordinateSide] at hx
    obtain ⟨q, hq, hs⟩ := (mem_aggregate_iff D _ x).mp hx
    refine ⟨q, ?_, hs⟩
    intro he
    subst q
    have bad : p i = !(p i) := (mem_filter.mp hq).2
    cases h : p i <;> simp [h] at bad

/-- A coordinate cut lifts to the original oriented separation, including its orientation. -/
theorem lift_coordinate (D : I → G.Separation) (i : I) :
    lift D (coordinateSide i false) = D i := by
  have extSides (s t : G.Separation) (ha : s.A = t.A) (hb : s.B = t.B) : s = t := by
    cases s
    cases t
    congr
  apply extSides
  · exact aggregate_coordinateSide D i false
  · change aggregate D (univ \ coordinateSide i false) = (D i).B
    rw [complement_coordinateSide, aggregate_coordinateSide]
    rfl

theorem coordinate_order (D : I → G.Separation) (i : I) :
    cutValue (weight D) (coordinateSide i false) = (D i).order := by
  rw [← order_lift, lift_coordinate]

section Realization

/-- One graph vertex for every unit of mass at every face. -/
abbrev Carrier (w : Face I → ℕ) := (f : Face I) × Fin (w f)

/-- A realization of prescribed weights on a finite edgeless graph. -/
def diagram (w : Face I → ℕ) (i : I) : (⊥ : SimpleGraph (Carrier w)).Separation where
  A := univ.filter fun x => x.1 i ≠ some true
  B := univ.filter fun x => x.1 i ≠ some false
  union_eq := by
    ext x
    simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
    cases h : x.1 i with
    | none => simp
    | some b => cases b <;> simp
  no_edge_across := fun _ => False.elim ‹False›

theorem faceOf_diagram (w : Face I → ℕ) (x : Carrier w) : faceOf (diagram w) x = x.1 := by
  funext i
  cases h : x.1 i with
  | none => simp [faceOf, diagram, h]
  | some b => cases b <;> simp [faceOf, diagram, h]

/-- Every natural weighting is recovered pointwise, in every finite dimension. -/
theorem weight_diagram (w : Face I → ℕ) : weight (diagram w) = w := by
  funext f
  unfold weight
  simp only [faceOf_diagram]
  let e : {x : Carrier w // x.1 = f} ≃ Fin (w f) := {
    toFun := fun ⟨⟨_, a⟩, h⟩ => h ▸ a
    invFun := fun a => ⟨⟨f, a⟩, rfl⟩
    left_inv := by rintro ⟨⟨_, _⟩, h⟩; cases h; rfl
    right_inv := fun _ => rfl }
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

theorem exists_edgeless_realization (w : Face I → ℕ) :
    ∃ (Y : Type u) (_ : Fintype Y) (_ : DecidableEq Y)
      (D : I → (⊥ : SimpleGraph Y).Separation), weight D = w :=
  ⟨Carrier w, inferInstance, inferInstance, diagram w, weight_diagram w⟩

end Realization

end CubicalDiagrams
