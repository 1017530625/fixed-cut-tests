import ProofBench.Research.CornerCrossing
import Mathlib.Data.Finset.SymmDiff

/-!
# Opposite corners and approximate containment of separations

Finite-graph versions of Lemmas 4.8, 4.9, 4.10 and Observation 4.11
of Bourneuf, Carmesin, Kurkofka and Planken.
-/

namespace CornerSection

open Finset CubicalDiagrams
open scoped symmDiff

variable {X : Type*} [Fintype X] [DecidableEq X] {G : SimpleGraph X}

/-- The meet of two oriented vertex separations, with first side the
intersection and second side the union of the corresponding input sides. -/
def meetSeparation (r s : G.Separation) : G.Separation where
  A := r.A ∩ s.A
  B := r.B ∪ s.B
  union_eq := by
    ext x
    have hr := mem_either r x
    have hs := mem_either s x
    simp only [mem_union, mem_inter, mem_univ, iff_true]
    tauto
  no_edge_across := by
    intro x y edge hx hy
    obtain ⟨hA, hB⟩ := mem_sdiff.mp hx
    obtain ⟨hr, hs⟩ := mem_inter.mp hA
    have ry := r.no_edge_across edge
      (mem_sdiff.mpr ⟨hr, fun h => hB (mem_union_left _ h)⟩)
    have sy := s.no_edge_across edge
      (mem_sdiff.mpr ⟨hs, fun h => hB (mem_union_right _ h)⟩)
    have coverR := mem_either r y
    have coverS := mem_either s y
    simp only [mem_sdiff, mem_union, mem_inter] at ry sy hy
    tauto

/-- Lemma 4.8. The two opposite corner orders sum to the two original
orders, for every choice of the two orientations. -/
theorem opposite_corner_orders (r s : G.Separation) (a b : Bool) :
    (cornerSeparator r s a b).card + (cornerSeparator r s (!a) (!b)).card =
      r.order + s.order := by
  have known := CubicalDiagrams.Square.opposite_corner_card_eq
    (fun i : Fin 2 => if i = 0 then (if a then r.flip else r)
      else (if b then s.flip else s))
  cases a <;> cases b <;>
    simpa [cornerSeparator, side, SimpleGraph.Separation.flip, SimpleGraph.Separation.order,
      SimpleGraph.Separation.separator, inter_comm] using known

theorem opposite_corner_orders_eq_twice (r s : G.Separation) (k : ℕ)
    (hr : r.order = k) (hs : s.order = k) (a b : Bool) :
    (cornerSeparator r s a b).card + (cornerSeparator r s (!a) (!b)).card = 2 * k := by
  rw [opposite_corner_orders, hr, hs, two_mul]

/-- The paper's approximate order of oriented separations. -/
def ApproxBelow (r s : G.Separation) (ε : ℕ) : Prop :=
  (r.A \ s.A).card ≤ ε ∧ (s.B \ r.B).card ≤ ε

def ApproxClose (r s : G.Separation) (ε : ℕ) : Prop :=
  ApproxBelow r s ε ∧ ApproxBelow s r ε

/-- Both symmetric differences have cardinality at most ε. -/
def EditAtMost (r s : G.Separation) (ε : ℕ) : Prop :=
  (r.A ∆ s.A).card ≤ ε ∧ (r.B ∆ s.B).card ≤ ε

omit [Fintype X] in
private theorem difference_triangle (a b c : Finset X) :
    (a \ c).card ≤ (a \ b).card + (b \ c).card := by
  apply le_trans _ (card_union_le (a \ b) (b \ c))
  apply card_le_card
  intro x hx
  simp only [mem_sdiff, mem_union] at hx ⊢
  by_cases h : x ∈ b <;> tauto

/-- Lemma 4.9. Approximate-containment errors add along a chain. -/
theorem approxBelow_trans (r s t : G.Separation) (ε δ : ℕ)
    (rs : ApproxBelow r s ε) (st : ApproxBelow s t δ) : ApproxBelow r t (ε + δ) := by
  obtain ⟨rsA, rsB⟩ := rs
  obtain ⟨stA, stB⟩ := st
  constructor
  · exact (difference_triangle r.A s.A t.A).trans (Nat.add_le_add rsA stA)
  · have h := difference_triangle t.B s.B r.B
    omega

/-- Lemma 4.10. Two approximate upper bounds give their meet with the sum
of the respective errors. -/
theorem approxBelow_meet (r s t : G.Separation) (ε δ : ℕ)
    (rs : ApproxBelow r s ε) (rt : ApproxBelow r t δ) :
    ApproxBelow r (meetSeparation s t) (ε + δ) := by
  obtain ⟨rsA, rsB⟩ := rs
  obtain ⟨rtA, rtB⟩ := rt
  have fwd : r.A \ (s.A ∩ t.A) = r.A \ s.A ∪ r.A \ t.A := by
    ext x
    simp only [mem_sdiff, mem_inter, mem_union]
    tauto
  have back : (s.B ∪ t.B) \ r.B = s.B \ r.B ∪ t.B \ r.B := by
    ext x
    simp only [mem_sdiff, mem_union]
    tauto
  change (r.A \ (s.A ∩ t.A)).card ≤ ε + δ ∧ ((s.B ∪ t.B) \ r.B).card ≤ ε + δ
  rw [fwd, back]
  exact ⟨(card_union_le _ _).trans (Nat.add_le_add rsA rtA),
    (card_union_le _ _).trans (Nat.add_le_add rsB rtB)⟩

/-- Observation 4.11(i). Closeness bounds edit-distance with factor two. -/
theorem edit_of_approxClose (s t : G.Separation) (ε : ℕ) (close : ApproxClose s t ε) :
    EditAtMost s t (2 * ε) := by
  obtain ⟨⟨sa, tb⟩, ⟨ta, sb⟩⟩ := close
  unfold EditAtMost
  rw [Finset.symmDiff_def, Finset.symmDiff_def, two_mul]
  exact ⟨(card_union_le _ _).trans (Nat.add_le_add sa ta),
    (card_union_le _ _).trans (Nat.add_le_add sb tb)⟩

/-- Observation 4.11(ii). Both directed differences fit in their common
symmetric difference. -/
theorem approxClose_of_edit (s t : G.Separation) (ε : ℕ) (edit : EditAtMost s t ε) :
    ApproxClose s t ε := by
  obtain ⟨ha, hb⟩ := edit
  exact ⟨⟨(card_le_card Finset.symmDiff_subset_sdiff).trans ha,
      (card_le_card Finset.symmDiff_subset_sdiff').trans hb⟩,
    ⟨(card_le_card Finset.symmDiff_subset_sdiff').trans ha,
      (card_le_card Finset.symmDiff_subset_sdiff).trans hb⟩⟩

end CornerSection
