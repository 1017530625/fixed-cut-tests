import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Separation
import ProofBench.PROBLEMS.P118.CubeTransversals

/-! Finite 3D corner diagrams of three oriented vertex separations.
See Bourneuf–Carmesin–Kurkofka–Planken, Lemmas 4.12 and 4.13. -/

namespace SeparationDiagrams
open Finset CornerLemma

variable {X : Type*} [Fintype X] [DecidableEq X] {G : SimpleGraph X}

/-- The false side is A, the true side B. -/
def side (s : G.Separation) (b : Bool) : Finset X := if b then s.B else s.A

private theorem belongs (s : G.Separation) (x : X) : x ∈ s.A ∨ x ∈ s.B := by
  apply mem_union.mp
  rw [s.union_eq]
  exact mem_univ x

/-- A coordinate is free at a separator vertex and fixed at each proper side. -/
def faceOf (D : Fin 3 → G.Separation) (x : X) : Face := fun i =>
  if x ∈ (D i).A then (if x ∈ (D i).B then none else some false) else some true

/-- On positive-dimensional faces this is the visualization map of the paper. -/
def weight (D : Fin 3 → G.Separation) (f : Face) : ℕ :=
  (univ.filter fun x => faceOf D x = f).card

theorem inFace_iff (D : Fin 3 → G.Separation) (v : Vertex) (x : X) :
    InFace v (faceOf D x) ↔ ∀ i, x ∈ side (D i) (v i) := by
  have each (i : Fin 3) :
      (faceOf D x i = none ∨ faceOf D x i = some (v i)) ↔ x ∈ side (D i) (v i) := by
    have h := belongs (D i) x
    cases bit : v i <;> by_cases ha : x ∈ (D i).A <;> by_cases hb : x ∈ (D i).B <;>
      simp_all [faceOf, side]
  exact forall_congr' each

/-- Union of the inclusive three-side intersections indexed by A. -/
def aggregate (D : Fin 3 → G.Separation) (A : Finset Vertex) : Finset X :=
  univ.filter fun x => ∃ v ∈ A, InFace v (faceOf D x)

theorem mem_aggregate_iff (D : Fin 3 → G.Separation) (A : Finset Vertex) (x : X) :
    x ∈ aggregate D A ↔ ∃ v ∈ A, ∀ i, x ∈ side (D i) (v i) := by
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

private theorem face_has_corner (f : Face) : ∃ v, InFace v f := by
  refine ⟨fun i => (f i).getD false, ?_⟩
  intro i
  cases h : f i <;> simp [h]

/-- The two corner unions cover the graph and no edge crosses between their
proper sides. This uses the actual no-cross-edge fields of the three separations. -/
def lift (D : Fin 3 → G.Separation) (A : Finset Vertex) : G.Separation where
  A := aggregate D A
  B := aggregate D (univ \ A)
  union_eq := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨v,hv⟩ := face_has_corner (faceOf D x)
    by_cases ha : v ∈ A
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, v, ha, hv⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, v, mem_sdiff.mpr ⟨mem_univ _, ha⟩, hv⟩)
  no_edge_across := by
    intro x y xy hx hy
    have shared := fun i => share_side (D i) xy
    choose v h using shared
    by_cases ha : v ∈ A
    · exact (mem_sdiff.mp hy).2 ((mem_aggregate_iff D A y).mpr ⟨v,ha,fun i => (h i).2⟩)
    · exact (mem_sdiff.mp hx).2 ((mem_aggregate_iff D _ x).mpr
        ⟨v,mem_sdiff.mpr ⟨mem_univ _,ha⟩,fun i => (h i).1⟩)

private def firstStep (p r : Vertex) : Vertex := fun i => if i = 0 then r i else p i
private def secondStep (p r : Vertex) : Vertex := fun i => if i = 2 then p i else r i

/-- A path of at most three edges inside the face joins any of its corners. -/
private theorem interpolates : ∀ (p r : Vertex) (f : Face), InFace p f → InFace r f →
    InFace (firstStep p r) f ∧ InFace (secondStep p r) f ∧
    (p = firstStep p r ∨ Adj p (firstStep p r)) ∧
    (firstStep p r = secondStep p r ∨ Adj (firstStep p r) (secondStep p r)) ∧
    (secondStep p r = r ∨ Adj (secondStep p r) r) := by
  have edges : ∀ p r : Vertex,
      (p = firstStep p r ∨ Adj p (firstStep p r)) ∧
      (firstStep p r = secondStep p r ∨ Adj (firstStep p r) (secondStep p r)) ∧
      (secondStep p r = r ∨ Adj (secondStep p r) r) := by decide
  intro p r f hp hr
  refine ⟨?_, ?_, edges p r⟩
  · intro i
    by_cases h : i = 0
    · simpa only [firstStep, if_pos h] using hr i
    · simpa only [firstStep, if_neg h] using hp i
  · intro i
    by_cases h : i = 2
    · simpa only [secondStep, if_pos h] using hp i
    · simpa only [secondStep, if_neg h] using hr i

private def active (A : Finset Vertex) : Finset Face :=
  univ.filter fun f => ∃ p r, Adj p r ∧ p ∈ A ∧ r ∉ A ∧ InFace p f ∧ InFace r f

private theorem active_iff (A : Finset Vertex) (f : Face) :
    f ∈ active A ↔ (∃ p ∈ A, InFace p f) ∧ ∃ r ∈ univ \ A, InFace r f := by
  simp only [active, mem_filter, mem_univ, true_and, mem_sdiff]
  constructor
  · rintro ⟨p,r,_,hp,hr,fp,fr⟩
    exact ⟨⟨p,hp,fp⟩,r,hr,fr⟩
  · rintro ⟨⟨p,hp,fp⟩,r,hr,fr⟩
    obtain ⟨f1,f2,e1,e2,e3⟩ := interpolates p r f fp fr
    have cross {x y : Vertex} (a : x ∈ A) (b : y ∉ A) (e : x = y ∨ Adj x y)
        (fx : InFace x f) (fy : InFace y f) :
        ∃ u w, Adj u w ∧ u ∈ A ∧ w ∉ A ∧ InFace u f ∧ InFace w f :=
      ⟨x,y,e.resolve_left (fun eq => b (eq ▸ a)),a,b,fx,fy⟩
    by_cases h1 : firstStep p r ∈ A
    · by_cases h2 : secondStep p r ∈ A
      · exact cross h2 hr e3 f2 fr
      · exact cross h1 h2 e2 f1 f2
    · exact cross hp h1 e1 fp f1

private theorem cut_eq_filter (D : Fin 3 → G.Separation) (A : Finset Vertex) :
    cutValue (weight D) A = (univ.filter fun x => faceOf D x ∈ active A).card := by
  exact sum_card_fiberwise_eq_card_filter univ (active A) (faceOf D)

/-- Finite graph version of Lemma 4.13. -/
theorem order_lift (D : Fin 3 → G.Separation) (A : Finset Vertex) :
    (lift D A).order = cutValue (weight D) A := by
  rw [cut_eq_filter]
  apply congrArg Finset.card
  ext x
  change x ∈ aggregate D A ∩ aggregate D (univ \ A) ↔ _
  simp only [mem_inter, aggregate, mem_filter, mem_univ, true_and, active_iff]

private def axisSide (i : Fin 3) : Finset Vertex := univ.filter fun v => v i = false

private theorem active_axis : ∀ (i : Fin 3) (f : Face), f ∈ active (axisSide i) ↔ f i = none := by
  decide

/-- Each coordinate value is the order of the corresponding input
separation. Equal orders therefore give Lemma 4.12. -/
theorem coordinate_order (D : Fin 3 → G.Separation) (i : Fin 3) :
    cutValue (weight D) (univ.filter fun v => v i = false) = (D i).order := by
  rw [cut_eq_filter]
  apply congrArg Finset.card
  ext x
  change x ∈ univ.filter (fun x => faceOf D x ∈ active (axisSide i)) ↔ x ∈ (D i).A ∩ (D i).B
  simp only [mem_filter, mem_univ, true_and, active_axis, mem_inter]
  by_cases ha : x ∈ (D i).A <;> by_cases hb : x ∈ (D i).B <;> simp [faceOf, ha, hb]

/-- The fixed test family is chosen independently of the finite graph, its
separations, and the cover. All numerical inputs are graph separation orders. -/
theorem flower_of_finite_separations (S : Finset (Finset Vertex))
    (hit : CornerCutLowerBound.HitsAll S) (D : Fin 3 → G.Separation)
    (R : Finset Vertex) (k : ℕ) (coord : ∀ i, (D i).order = k)
    (cover : ∀ u v, Adj u v → u ∈ R ∨ v ∈ R)
    (atom : ∀ r ∈ R, k ≤ (lift D {r}).order)
    (pair : ∀ A ∈ S, (∃ r ∈ R, r ∈ A) → (∃ r ∈ R, r ∉ A) → k ≤ (lift D A).order) :
    IsFlower (weight D) k := by
  apply CubeTransversals.sufficient_of_hitsAll S hit (weight D) k R
  · exact fun i => (coordinate_order D i).trans (coord i)
  · exact cover
  · intro r hr
    rw [← order_lift]
    exact atom r hr
  · intro A hA h₁ h₂
    rw [← order_lift]
    exact pair A hA h₁ h₂

end SeparationDiagrams

