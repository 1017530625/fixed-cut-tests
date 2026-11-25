import ProofBench.Research.CornerCrossing
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# A twenty-four-cycle satisfying the 3D Corner Lemma

The six ring corners of the cube occur in cyclic order 1, 3, 2, 6, 4, 5
(binary coordinates). A graph vertex at a ring edge gets both its endpoints
as labels. Three more vertices on the following path get its endpoint as
their single label. Thus the host is the ordinary cycle on 24 vertices.
-/

namespace CornerSection.Cycle24

open Finset CubicalDiagrams SimpleGraph

abbrev host : SimpleGraph (Fin 24) := cycleGraph 24

private def ringCode (n : ℕ) : ℕ :=
  match n % 6 with
  | 0 => 1
  | 1 => 3
  | 2 => 2
  | 3 => 6
  | 4 => 4
  | _ => 5

private def ringBit (n : ℕ) (i : Fin 3) : Bool := (ringCode n).testBit (2 - i.val)

private def coordinate (i : Fin 3) (b : Bool) : Finset (Fin 24) :=
  univ.filter fun x =>
    let n := x.val / 4
    ringBit (n + 1) i = b ∨ (x.val % 4 = 0 ∧ ringBit n i = b)

set_option maxRecDepth 16000
set_option maxHeartbeats 7000000

private theorem coordinate_cover :
    ∀ i : Fin 3, coordinate i false ∪ coordinate i true = univ := by decide

private theorem coordinate_edges : ∀ (i : Fin 3) (x y : Fin 24),
    host.Adj x y → x ∈ coordinate i false \ coordinate i true →
      y ∉ coordinate i true \ coordinate i false := by decide

/-- The three coordinate separations on the subdivided ring. -/
def diagram (i : Fin 3) : host.Separation where
  A := coordinate i false
  B := coordinate i true
  union_eq := coordinate_cover i
  no_edge_across := fun {x y} => coordinate_edges i x y

/-- Enumerate the surviving vertices in path order after removing c. -/
private def skip (c : Fin 24) (i : Fin 23) : Fin 24 := c + 1 + i.castSucc

private theorem skip_ne : ∀ c i, skip c i ≠ c := by decide

private theorem skip_onto :
    ∀ (c x : Fin 24), x ≠ c → ∃ i, skip c i = x := by decide

private theorem skip_edges : ∀ (c : Fin 24) (i j : Fin 23),
    (pathGraph 23).Adj i j → host.Adj (skip c i) (skip c j) := by
  simp only [pathGraph_adj]
  decide

/-- The distinguished path, read cyclically from c+1 through c-1, visits
every surviving vertex; the proof quantifies over no candidate separations. -/
theorem deletion_preconnected (c : Fin 24) : (host.induce {x | x ≠ c}).Preconnected := by
  let embed : pathGraph 23 →g host.induce {x | x ≠ c} :=
    { toFun := fun i => ⟨skip c i, skip_ne c i⟩
      map_rel' := fun {i j} h => skip_edges c i j h }
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨i, rfl⟩ := skip_onto c x hx
  obtain ⟨j, rfl⟩ := skip_onto c y hy
  exact (pathGraph_preconnected 23 i j).map embed

private theorem third_vertex :
    ∀ (x y : Fin 24), ∃ c : Fin 24, x ≠ c ∧ y ≠ c := by decide

/-- An order-at-most-one separation of this cycle has an empty proper side.
A walk in the remaining path would otherwise cross the two proper sides. -/
theorem unbreakable : Unbreakable host 0 1 := by
  intro s small
  by_contra! h
  obtain ⟨x, hx⟩ := card_pos.mp h.1
  obtain ⟨y, hy⟩ := card_pos.mp h.2
  have xs : x ∉ s.separator := fun hz => (mem_sdiff.mp hx).2 (mem_inter.mp hz).2
  have ys : y ∉ s.separator := fun hz => (mem_sdiff.mp hy).2 (mem_inter.mp hz).1
  have removed : ∃ c, x ≠ c ∧ y ≠ c ∧ ∀ z ∈ s.separator, z = c := by
    by_cases empty : s.separator = ∅
    · obtain ⟨c, xc, yc⟩ := third_vertex x y
      exact ⟨c, xc, yc, by simp [empty]⟩
    · obtain ⟨c, hc⟩ := nonempty_iff_ne_empty.mpr empty
      exact ⟨c, fun e => xs (e ▸ hc), fun e => ys (e ▸ hc),
        fun z hz => Finset.card_le_one.mp small z hz c hc⟩
  obtain ⟨c, xc, yc, covers⟩ := removed
  obtain ⟨walk⟩ := deletion_preconnected c ⟨x, xc⟩ ⟨y, yc⟩
  obtain ⟨d, _, hA, hnA⟩ := walk.exists_boundary_dart {v | v.val ∈ s.A}
    (mem_sdiff.mp hx).1 (mem_sdiff.mp hy).2
  have hnB : d.fst.val ∉ s.B := fun hb =>
    d.fst.property (covers _ (mem_inter.mpr ⟨hA, hb⟩))
  exact s.no_edge_across d.adj (mem_sdiff.mpr ⟨hA, hnB⟩)
    (mem_sdiff.mpr ⟨(mem_either s d.snd.val).resolve_left hnA, hnA⟩)

private instance (s t : host.Separation) : Decidable (Cross s t) := by
  unfold Cross Nested OrientedBelow
  infer_instance

/-- All three distinct pairs genuinely cross. -/
theorem crosses : ∀ i j : Fin 3, i ≠ j → Cross (diagram i) (diagram j) := by decide

theorem orders : ∀ i : Fin 3, (diagram i).order = 2 := by decide

private theorem corner_orders : ∀ i j : Fin 3, i ≠ j → ∀ a b,
    (cornerSeparator (diagram i) (diagram j) a b).card = 2 := by decide

/-- Among the four proper corners of a pair, the two sides with matching
bits contain three vertices each, and the other two contain seven each. -/
theorem proper_sizes : ∀ i j : Fin 3, i ≠ j → ∀ a b,
    (properCorner (diagram i) (diagram j) a b).card = if a = b then 3 else 7 := by decide

/-- Each induced partition in this example has empty centre and two singleton links. -/
theorem partition_sizes : ∀ i j : Fin 3, i ≠ j →
    (centre (diagram i) (diagram j)).card = 0 ∧
    (link (diagram i) (diagram j) false).card = 1 ∧
    (link (diagram i) (diagram j) true).card = 1 := by decide

theorem equitable : Equitable diagram 2 := by
  intro i j cross
  apply corner_orders
  rintro rfl
  exact cross_irrefl _ cross

theorem criss : CrissCompatible diagram (2 * 0 + 2) := by
  intro i j cross a b
  have distinct : i ≠ j := by
    rintro rfl
    exact cross_irrefl _ cross
  rw [proper_sizes i j distinct a b]
  split <;> decide

/-- All six non-polar edges have mass one. -/
theorem nonzero_profile :
    weight diagram (fun _ => none) = 0 ∧
    (∀ f, CornerLemma.dim f = 2 → weight diagram f = 0) ∧
    (∀ f, CornerLemma.dim f = 1 →
      weight diagram f = if CornerLemma.InFace (fun _ => false) f ∨
        CornerLemma.InFace (fun _ => true) f then 0 else 1) := by decide

theorem flower : CornerLemma.IsFlower (weight diagram) 2 :=
  ⟨nonzero_profile.2.1, fun _ => false, 1, by decide, nonzero_profile.1, nonzero_profile.2.2⟩

end CornerSection.Cycle24