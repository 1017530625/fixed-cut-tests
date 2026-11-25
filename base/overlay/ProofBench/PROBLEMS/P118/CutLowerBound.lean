import ProofBench.PROBLEMS.P118.P118
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace CornerCutLowerBound

open CornerLemma Finset

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

private def triple {α : Type} (a b c : α) (i : Fin 3) : α :=
  if i.val = 0 then a else if i.val = 1 then b else c

private abbrev v0 : Vertex := triple false false false
private abbrev v1 : Vertex := triple false false true
private abbrev v2 : Vertex := triple false true false
private abbrev v3 : Vertex := triple false true true
private abbrev v4 : Vertex := triple true false false
private abbrev v5 : Vertex := triple true false true
private abbrev v6 : Vertex := triple true true false
private abbrev v7 : Vertex := triple true true true

private abbrev e0 : Face := triple (.some false) (.some false) none
private abbrev e1 : Face := triple (.some false) none (.some false)
private abbrev e2 : Face := triple none (.some false) (.some false)
private abbrev e3 : Face := triple (.some false) none (.some true)
private abbrev e4 : Face := triple none (.some false) (.some true)
private abbrev e5 : Face := triple (.some false) (.some true) none
private abbrev e6 : Face := triple none (.some true) (.some false)
private abbrev e7 : Face := triple none (.some true) (.some true)
private abbrev e8 : Face := triple (.some true) (.some false) none
private abbrev e9 : Face := triple (.some true) none (.some false)
private abbrev e10 : Face := triple (.some true) none (.some true)
private abbrev e11 : Face := triple (.some true) (.some true) none

private def edgeSide (i : Fin 12) : Finset Vertex :=
  match i.val with
  | 0 => {v0, v1}
  | 1 => {v0, v2}
  | 2 => {v0, v4}
  | 3 => {v1, v3}
  | 4 => {v1, v5}
  | 5 => {v2, v3}
  | 6 => {v2, v6}
  | 7 => {v3, v7}
  | 8 => {v4, v5}
  | 9 => {v4, v6}
  | 10 => {v5, v7}
  | _ => {v6, v7}

private def cover (i : Fin 8) : Finset Vertex :=
  match i.val with
  | 0 => {v1, v2, v3, v4, v5, v6}
  | 1 => {v1, v2, v3, v4, v5, v6}
  | 2 => {v0, v2, v3, v4, v5, v7}
  | 3 => {v0, v2, v3, v4, v5, v7}
  | 4 => {v0, v1, v3, v4, v6, v7}
  | 5 => {v0, v1, v3, v4, v6, v7}
  | 6 => {v0, v1, v2, v5, v6, v7}
  | _ => {v0, v1, v2, v5, v6, v7}

private def makeWeight (i : Fin 8) : Face → ℕ :=
  match i.val with
  | 0 => fun f => if f = e3 ∨ f = e6 ∨ f = e8 then 1 else 0
  | 1 => fun f => if f = e4 ∨ f = e5 ∨ f = e9 then 1 else 0
  | 2 => fun f => if f = e1 ∨ f = e7 ∨ f = e8 then 1 else 0
  | 3 => fun f => if f = e2 ∨ f = e5 ∨ f = e10 then 1 else 0
  | 4 => fun f => if f = e0 ∨ f = e7 ∨ f = e9 then 1 else 0
  | 5 => fun f => if f = e2 ∨ f = e3 ∨ f = e11 then 1 else 0
  | 6 => fun f => if f = e0 ∨ f = e6 ∨ f = e10 then 1 else 0
  | _ => fun f => if f = e1 ∨ f = e4 ∨ f = e11 then 1 else 0

private def badSides (i : Fin 8) : Finset (Finset Vertex) :=
  match i.val with
  | 0 => {edgeSide 3, edgeSide 6, edgeSide 8}
  | 1 => {edgeSide 4, edgeSide 5, edgeSide 9}
  | 2 => {edgeSide 1, edgeSide 7, edgeSide 8}
  | 3 => {edgeSide 2, edgeSide 5, edgeSide 10}
  | 4 => {edgeSide 0, edgeSide 7, edgeSide 9}
  | 5 => {edgeSide 2, edgeSide 3, edgeSide 11}
  | 6 => {edgeSide 0, edgeSide 6, edgeSide 10}
  | _ => {edgeSide 1, edgeSide 4, edgeSide 11}


/-- A fixed test sees one side of a cut consisting exactly of the two ends of a cube edge. -/
def AdjacentSide (A : Finset Vertex) : Prop :=
  ∃ u v, Adj u v ∧ A = {u,v}

/-- The three edge sides on which witness j has cut value zero. -/
def AlternatingMatching (j : Fin 8) : Finset (Finset Vertex) := badSides j

/-- A static test family hits each of the eight alternating matchings. -/
def HitsAll (S : Finset (Finset Vertex)) : Prop :=
  ∀ j, ∃ A ∈ AlternatingMatching j, A ∈ S

private def eliminated (A : Finset Vertex) : Finset (Fin 8) :=
  univ.filter (fun j => A ∈ badSides j)

private theorem pair_index : ∀ u v : Vertex, Adj u v → ∃ e : Fin 12, edgeSide e = {u,v} := by
  decide

private theorem eliminated_card_index : ∀ e : Fin 12, (eliminated (edgeSide e)).card = 2 := by
  decide

private theorem coords_table : ∀ j : Fin 8, ∀ i : Fin 3,
    cutValue (makeWeight j) (univ.filter fun v => v i = false) = 1 := by
  decide

private theorem cover_table : ∀ j : Fin 8, ∀ u v : Vertex, Adj u v → u ∈ cover j ∨ v ∈ cover j := by
  decide

private theorem single_table : ∀ j : Fin 8, ∀ u : Vertex,
    u ∈ cover j → 1 ≤ cutValue (makeWeight j) {u} := by
  decide

private theorem pair_table : ∀ j : Fin 8, ∀ e : Fin 12,
    edgeSide e ∉ badSides j → 1 ≤ cutValue (makeWeight j) (edgeSide e) := by
  decide

private theorem not_flower (j : Fin 8) : ¬ IsFlower (makeWeight j) 1 := by
  have cube : ∀ i : Fin 8, makeWeight i (fun _ => none) = 0 := by decide
  rintro ⟨_, _, l, small, full, _⟩
  rw [cube] at full
  omega

/-- Every static family that misses a matching admits that matching's counterexample. -/
theorem counterexample_of_not_hitsAll (S : Finset (Finset Vertex))
    (pairs : ∀ A ∈ S, AdjacentSide A) (miss : ¬ HitsAll S) :
    ∃ (lam : Face → ℕ) (R : Finset Vertex),
      (∀ i : Fin 3, cutValue lam (univ.filter fun v => v i = false) = 1) ∧
      (CubeCertificate.EdgeCover R) ∧
      (∀ u ∈ R, 1 ≤ cutValue lam {u}) ∧
      (∀ A ∈ S, 1 ≤ cutValue lam A) ∧
      ¬ IsFlower lam 1 := by
  classical
  obtain ⟨j, hj⟩ := not_forall.mp miss
  refine ⟨makeWeight j, cover j, coords_table j, cover_table j, single_table j, ?_, not_flower j⟩
  intro A hA
  obtain ⟨u, v, adj, rfl⟩ := pairs A hA
  obtain ⟨e, he⟩ := pair_index u v adj
  rw [← he]
  apply pair_table
  intro hbad
  exact hj ⟨_, he ▸ hbad, hA⟩

/-- Each adjacent two-vertex side hits exactly two of the eight matchings. -/
theorem adjacent_hits_two {A : Finset Vertex} (adjacent : AdjacentSide A) :
    (univ.filter (fun j : Fin 8 => A ∈ AlternatingMatching j)).card = 2 := by
  obtain ⟨u, v, huv, rfl⟩ := adjacent
  obtain ⟨e, he⟩ := pair_index u v huv
  rw [← he]
  exact eliminated_card_index e

theorem small_misses (S : Finset (Finset Vertex))
    (size : S.card ≤ 3) (pairs : ∀ A ∈ S, AdjacentSide A) : ¬ HitsAll S := by
  classical
  have covered : (S.biUnion eliminated).card ≤ S.card * 2 := by
    apply card_biUnion_le_card_mul
    intro A hA
    obtain ⟨u, v, adj, rfl⟩ := pairs A hA
    obtain ⟨e, he⟩ := pair_index u v adj
    rw [← he, eliminated_card_index]
  have missed : ∃ j : Fin 8, j ∉ S.biUnion eliminated := by
    by_contra! hall
    have heq : S.biUnion eliminated = univ := Finset.eq_univ_of_forall hall
    rw [heq] at covered
    simp at covered
    omega
  obtain ⟨j, hj⟩ := missed
  intro hits
  obtain ⟨A, ha, hA⟩ := hits j
  exact hj (mem_biUnion.mpr ⟨A, hA, mem_filter.mpr ⟨mem_univ _, ha⟩⟩)

/-- With all applicable singleton inequalities present, any fixed family of at most
three adjacent two-vertex sides still admits a counterexample at k=1. -/
theorem three_tests_insufficient (S : Finset (Finset Vertex))
    (size : S.card ≤ 3) (pairs : ∀ A ∈ S, AdjacentSide A) :
    ∃ (lam : Face → ℕ) (R : Finset Vertex),
      (∀ i : Fin 3, cutValue lam (univ.filter fun v => v i = false) = 1) ∧
      (CubeCertificate.EdgeCover R) ∧
      (∀ u ∈ R, 1 ≤ cutValue lam {u}) ∧
      (∀ A ∈ S, 1 ≤ cutValue lam A) ∧
      ¬ IsFlower lam 1 :=
  counterexample_of_not_hitsAll S pairs (small_misses S size pairs)

#print axioms adjacent_hits_two
#print axioms counterexample_of_not_hitsAll
#print axioms three_tests_insufficient

end CornerCutLowerBound
