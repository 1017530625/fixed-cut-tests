import ProofBench.Research.LargeCornersP118
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Fintype.Powerset

/-! A graph with a nonzero flower parameter and an intrinsic six-corner cover. -/
namespace CubicalDiagrams.CycleExample

open Finset

abbrev host : SimpleGraph (Fin 6) := SimpleGraph.cycleGraph 6

/-- The six corners in the order in which the cube ring visits them. -/
private def ringNumber (i : Fin 6) : ℕ :=
  match i.val with
  | 0 => 1
  | 1 => 3
  | 2 => 2
  | 3 => 6
  | 4 => 4
  | _ => 5

private def corner (n : ℕ) : Corner (Fin 3) := fun i => n.testBit (2 - i.val)

/-- Host vertex x denotes the ring edge from corner x to the next corner.
A side contains all host edges with an endpoint of the chosen bit. -/
private def coordinate (i : Fin 3) (b : Bool) : Finset (Fin 6) :=
  univ.filter fun x => corner (ringNumber x) i = b ∨ corner (ringNumber (x + 1)) i = b

private theorem coordinate_cover : ∀ i : Fin 3,
    coordinate i false ∪ coordinate i true = univ := by decide

private theorem coordinate_no_edge : ∀ (i : Fin 3) (x y : Fin 6),
    host.Adj x y → x ∈ coordinate i false \ coordinate i true →
      y ∉ coordinate i true \ coordinate i false := by decide

def diagram (i : Fin 3) : host.Separation where
  A := coordinate i false
  B := coordinate i true
  union_eq := coordinate_cover i
  no_edge_across := fun {x y} => coordinate_no_edge i x y

set_option maxRecDepth 20000
set_option maxHeartbeats 7000000

/-- Every separation of order at most one on the six-cycle has an empty proper side. -/
theorem unbreakable : Unbreakable host 0 1 := by
  have sides : ∀ (A B : Finset (Fin 6)), A ∪ B = univ → (A ∩ B).card ≤ 1 →
      (∀ x y, host.Adj x y → x ∈ A \ B → y ∉ B \ A) →
      (A \ B).card ≤ 0 ∨ (B \ A).card ≤ 0 := by decide
  intro s small
  exact sides s.A s.B s.union_eq small (fun _ _ => s.no_edge_across)

theorem coordinates : ∀ i : Fin 3, (diagram i).order = 2 := by decide

/-- Each ring corner contains its two incident hosts; the two omitted corners are empty. -/
theorem region_card : ∀ p : Corner (Fin 3),
    (region diagram p).card = if p = corner 0 ∨ p = corner 7 then 0 else 2 := by decide

theorem large_corners : largeCorners diagram 0 2 = univ \ {corner 0, corner 7} := by
  ext p
  simp [largeCorners, region_card]
  split_ifs <;> simp_all
  tauto

private theorem ring_cover : ∀ p r : Corner (Fin 3), CornerLemma.Adj p r →
    p ∈ univ \ {corner 0, corner 7} ∨ r ∈ univ \ {corner 0, corner 7} := by decide

theorem natural_cover : ∀ p r, CornerLemma.Adj p r →
    p ∈ largeCorners diagram 0 2 ∨ r ∈ largeCorners diagram 0 2 := by
  simpa [large_corners] using ring_cover

/-- This application discharges the large-corner cover from the concrete graph diagram. -/
theorem flower : CornerLemma.IsFlower (weight diagram) 2 :=
  P118.flower_of_large_corner_cover diagram 0 2 unbreakable coordinates natural_cover

/-- The flower has ell = 1 and zero whole-cube weight. The six ring edges have
unit weight, the cube edges incident with the omitted opposite corners have zero weight. -/
theorem nonzero_flower_profile :
    weight diagram (fun _ => none) = 0 ∧
    (∀ f, CornerLemma.dim f = 1 →
      weight diagram f = if InFace (corner 0) f ∨ InFace (corner 7) f then 0 else 1) ∧
    (∀ f, CornerLemma.dim f = 2 → weight diagram f = 0) := by decide

end CubicalDiagrams.CycleExample
