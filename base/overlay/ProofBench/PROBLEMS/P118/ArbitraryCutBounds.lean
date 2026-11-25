import ProofBench.PROBLEMS.P118.CutRequirements
import ProofBench.PROBLEMS.P118.MinimumDesigns

/-! Bounds and canonical representatives for arbitrary unordered corner cuts. -/
namespace CornerArbitraryCuts

open Finset CornerLemma CornerCutLowerBound

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

/-- The orientation of an unordered cut used for the census excludes corner 000. -/
def canonicalSides : Finset (Finset Vertex) :=
  univ.filter fun A => A.Nonempty ∧ (fun _ : Fin 3 => false) ∉ A

theorem canonicalSides_card : canonicalSides.card = 127 := by decide

theorem detected_compl : ∀ A : Finset Vertex, detected Aᶜ = detected A := by decide

/-- Every oriented side detects either zero or exactly two witnesses. -/
theorem detected_card_zero_or_two : ∀ A : Finset Vertex,
    (detected A).card = 0 ∨ (detected A).card = 2 := by decide

theorem detected_card_le_two (A : Finset Vertex) : (detected A).card ≤ 2 := by
  rcases detected_card_zero_or_two A with h | h <;> omega

theorem detected_union_bound (S : Finset (Finset Vertex)) :
    (S.biUnion detected).card ≤ 2 * S.card := by
  rw [Nat.mul_comm]
  exact card_biUnion_le_card_mul _ _ _ fun A _ => detected_card_le_two A

theorem complete_iff_union (S : Finset (Finset Vertex)) :
    Complete S ↔ S.biUnion detected = univ := by
  constructor
  · intro h
    exact eq_univ_of_forall fun j => mem_biUnion.mpr (h j)
  · intro h j
    apply mem_biUnion.mp
    rw [h]
    exact mem_univ _

theorem complete_card_ge_four (S : Finset (Finset Vertex)) (hc : Complete S) :
    4 ≤ S.card := by
  have h := detected_union_bound S
  rw [(complete_iff_union S).mp hc] at h
  simp at h
  omega

/-- All three parallel classes and all six face boundaries attain the global lower bound. -/
theorem nine_designs_complete : ∀ S ∈ CubeMinimumDesigns.nineDesigns,
    S.card = 4 ∧ Complete S := by
  intro S h
  simp only [CubeMinimumDesigns.nineDesigns, mem_insert, mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold Complete <;> decide

/-- The two alternating witnesses on a specified six-ring. -/
def CompleteAt (q : Fin 4) (S : Finset (Finset Vertex)) : Prop :=
  ∀ b : Bool, ∃ A ∈ S, CoverAware.index q b ∈ detected A

theorem opposite_witnesses_incompatible : ∀ (A : Finset Vertex) (q : Fin 4),
    CoverAware.index q false ∈ detected A → CoverAware.index q true ∉ detected A := by decide

theorem completeAt_card_ge_two (q : Fin 4) (S : Finset (Finset Vertex))
    (h : CompleteAt q S) : 2 ≤ S.card := by
  obtain ⟨A, hA, ha⟩ := h false
  obtain ⟨B, hB, hb⟩ := h true
  exact one_lt_card.mpr ⟨A, hA, B, hB, fun he => opposite_witnesses_incompatible A q ha (he ▸ hb)⟩

#print axioms canonicalSides_card
#print axioms detected_compl
#print axioms detected_card_zero_or_two
#print axioms complete_card_ge_four
#print axioms nine_designs_complete
#print axioms completeAt_card_ge_two

end CornerArbitraryCuts
