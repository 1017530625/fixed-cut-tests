import ProofBench.PROBLEMS.P118.GraphTests
import Mathlib.Combinatorics.SimpleGraph.Star

/-! Fixed adjacent-pair tests for three separations, restricted to connected hosts. -/

namespace ConnectedCornerTests

open Finset CornerLemma CornerCutLowerBound SeparationDiagrams

/-- All eight instances use the same four-vertex tree. -/
abbrev host : SimpleGraph (Fin 4) := SimpleGraph.starGraph 0

private def corner (n : ℕ) : Vertex := fun i => n.testBit (2 - i.val)

/-- Face spanned by the endpoints of a cube edge. -/
private def edgeFace (a b : ℕ) : Face := fun i =>
  if corner a i = corner b i then some (corner a i) else none

private def three {α : Type} (a b c : α) (x : Fin 4) : α :=
  if x = 1 then a else if x = 2 then b else c

/-- The centre is labelled by the whole cube. Each leaf receives one
edge of the alternating matching of the selected six-cycle. -/
def label (j : Fin 8) (x : Fin 4) : Face :=
  if x = 0 then fun _ => none else
    match j.val with
    | 0 => three (edgeFace 1 3) (edgeFace 2 6) (edgeFace 4 5) x
    | 1 => three (edgeFace 1 5) (edgeFace 2 3) (edgeFace 4 6) x
    | 2 => three (edgeFace 0 2) (edgeFace 3 7) (edgeFace 4 5) x
    | 3 => three (edgeFace 0 4) (edgeFace 2 3) (edgeFace 5 7) x
    | 4 => three (edgeFace 0 1) (edgeFace 3 7) (edgeFace 4 6) x
    | 5 => three (edgeFace 0 4) (edgeFace 1 3) (edgeFace 6 7) x
    | 6 => three (edgeFace 0 1) (edgeFace 2 6) (edgeFace 5 7) x
    | _ => three (edgeFace 0 2) (edgeFace 1 5) (edgeFace 6 7) x

/-- The six vertices incident with the chosen alternating perfect matching. -/
def cover (j : Fin 8) : Finset Vertex := (AlternatingMatching j).biUnion id

/-- The centre belongs to both sides at each coordinate, so a star edge
cannot cross between the two proper sides. -/
def diagram (j : Fin 8) (i : Fin 3) : host.Separation where
  A := univ.filter fun x => label j x i ≠ some true
  B := univ.filter fun x => label j x i ≠ some false
  union_eq := by
    ext x
    simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
    cases h : label j x i with
    | none => simp
    | some b => cases b <;> simp
  no_edge_across := by
    intro x y xy hx hy
    have ends := (SimpleGraph.starGraph_adj.mp xy).2
    rcases ends with rfl | rfl
    · exact (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨mem_univ _, by simp [label]⟩)
    · exact (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨mem_univ _, by simp [label]⟩)

set_option maxRecDepth 30000
set_option maxHeartbeats 6000000

private theorem coordinates : ∀ (j : Fin 8) (i : Fin 3), (diagram j i).order = 2 := by decide
private theorem six : ∀ j, (cover j).card = 6 := by decide
private theorem covers : ∀ (j : Fin 8) (u v : Vertex), Adj u v → u ∈ cover j ∨ v ∈ cover j := by
  decide
private theorem singles : ∀ (j : Fin 8) (u : Vertex), u ∈ cover j →
    (lift (diagram j) {u}).order = 2 := by decide
private theorem edgeOrders : ∀ (j : Fin 8) (u v : Vertex), Adj u v →
    (if {u,v} ∈ AlternatingMatching j then (lift (diagram j) {u,v}).order = 1
     else 2 ≤ (lift (diagram j) {u,v}).order) := by decide
/-- In each witness the centre is the only vertex on the full cube face. -/
theorem centre_weight : ∀ j : Fin 8, weight (diagram j) (fun _ => none) = 1 := by decide

/-- Every missed matching has a counterexample on the same four-vertex star.
All singleton orders on the six-cycle are exactly two; precisely the matching
edges fail the adjacent-pair threshold. -/
theorem star_obstruction (j : Fin 8) :
    host.IsTree ∧ (cover j).card = 6 ∧ (∀ i, (diagram j i).order = 2) ∧
    (∀ u v, Adj u v → u ∈ cover j ∨ v ∈ cover j) ∧
    (∀ u ∈ cover j, (lift (diagram j) {u}).order = 2) ∧
    (∀ u v, Adj u v → (2 ≤ (lift (diagram j) {u,v}).order ↔ {u,v} ∉ AlternatingMatching j)) ∧
    ¬ IsFlower (weight (diagram j)) 2 := by
  refine ⟨SimpleGraph.isTree_starGraph _, six j, coordinates j, covers j, singles j, ?_, ?_⟩
  · intro u v adj
    have h := edgeOrders j u v adj
    by_cases mem : {u,v} ∈ AlternatingMatching j <;> simp [mem] at h ⊢
    · omega
    · exact h
  · rintro ⟨_, _, l, bound, full, _⟩
    rw [centre_weight] at full
    omega

/-- Sufficiency tested on all diagrams and covers of one specified host. -/
def SufficientOn {X : Type} [Fintype X] [DecidableEq X] (G : SimpleGraph X)
    (S : Finset (Finset Vertex)) : Prop :=
  ∀ (D : Fin 3 → G.Separation) (R : Finset Vertex) (k : ℕ),
    (∀ i, (D i).order = k) →
    (∀ u v, Adj u v → u ∈ R ∨ v ∈ R) →
    (∀ u ∈ R, k ≤ (lift D {u}).order) →
    (∀ A ∈ S, (∃ u ∈ R, u ∈ A) → (∃ v ∈ R, v ∉ A) → k ≤ (lift D A).order) →
    IsFlower (weight D) k

/-- Testing just one four-vertex tree already characterizes every fixed
family of adjacent-pair tests. -/
theorem on_star_iff (S : Finset (Finset Vertex)) (pairs : ∀ A ∈ S, AdjacentSide A) :
    SufficientOn host S ↔ HitsAll S := by
  constructor
  · intro works
    by_contra miss
    obtain ⟨j, missed⟩ := not_forall.mp miss
    obtain ⟨_, _, coord, cv, atom, edge, bad⟩ := star_obstruction j
    apply bad (works (diagram j) (cover j) 2 coord cv (fun u hu => (atom u hu).ge) ?_)
    intro A hA _ _
    obtain ⟨u, v, huv, rfl⟩ := pairs A hA
    exact (edge u v huv).mpr (fun h => missed ⟨_, h, hA⟩)
  · intro hits
    exact (GraphCornerTests.iff_hitsAll S pairs).mpr hits (Fin 4) host

/-- Sufficiency restricted to connected finite simple graphs. -/
def ConnectedSufficient (S : Finset (Finset Vertex)) : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (G : SimpleGraph X), G.Connected → SufficientOn G S

theorem connected_iff_hitsAll (S : Finset (Finset Vertex)) (pairs : ∀ A ∈ S, AdjacentSide A) :
    ConnectedSufficient S ↔ HitsAll S := by
  constructor
  · intro works
    exact (on_star_iff S pairs).mp (works (Fin 4) host (SimpleGraph.connected_starGraph _))
  · intro hits X _ _ G _
    exact (GraphCornerTests.iff_hitsAll S pairs).mpr hits X G

theorem connected_at_least_four (S : Finset (Finset Vertex)) (pairs : ∀ A ∈ S, AdjacentSide A)
    (works : ConnectedSufficient S) : 4 ≤ S.card := by
  exact GraphCornerTests.at_least_four S pairs
    ((GraphCornerTests.iff_hitsAll S pairs).mpr ((connected_iff_hitsAll S pairs).mp works))

theorem connected_four_iff_listed (S : Finset (Finset Vertex)) (card : S.card = 4)
    (pairs : ∀ A ∈ S, AdjacentSide A) :
    ConnectedSufficient S ↔ S ∈ CubeMinimumDesigns.nineDesigns :=
  (connected_iff_hitsAll S pairs).trans
    ((GraphCornerTests.iff_hitsAll S pairs).symm.trans (GraphCornerTests.four_iff_listed S card pairs))

end ConnectedCornerTests

#print axioms ConnectedCornerTests.centre_weight
#print axioms ConnectedCornerTests.star_obstruction
#print axioms ConnectedCornerTests.on_star_iff
#print axioms ConnectedCornerTests.connected_iff_hitsAll
#print axioms ConnectedCornerTests.connected_at_least_four
#print axioms ConnectedCornerTests.connected_four_iff_listed
