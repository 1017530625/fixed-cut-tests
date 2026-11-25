import ProofBench.PROBLEMS.P118.GeneralGraphCuts
import ProofBench.PROBLEMS.P118.ArbitraryCutProfile

/-! The optimal four-cut families are perfect matchings on the eight witnesses,
with a choice of an actual cut for each witness pair. -/
namespace CornerArbitraryCuts

open Finset CornerLemma SignatureTable

/-- Binary label in the paper's table, mapped to the corresponding Lean witness. -/
def labelIndex (i : Fin 8) : Fin 8 :=
  ![0, 2, 6, 4, 5, 7, 3, 1] i

theorem labelIndex_bijective : Function.Bijective labelIndex := by
  constructor <;> decide

def labelDistance (i j : Fin 8) : ℕ :=
  ((univ : Finset (Fin 3)).filter fun b => i.val.testBit b.val ≠ j.val.testBit b.val).card

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
-- Kernel reduction verifies the 127 incidence rows for each of the 28 label pairs.
/-- Multiplicity of an unordered pair of distinct witnesses in the actual cut incidence graph. -/
theorem pair_multiplicity (i j : Fin 8) (ne : i ≠ j) :
    (canonicalSides.filter fun A => labelIndex i ∈ detected A ∧ labelIndex j ∈ detected A).card =
      if labelDistance i j = 1 then 3 else if labelDistance i j = 2 then 1 else 0 := by
  let active (t : Fin 127) :=
    (signatureMask t).testBit (labelIndex i).val && (signatureMask t).testBit (labelIndex j).val
  have actual :
      (canonicalSides.filter fun A => labelIndex i ∈ detected A ∧ labelIndex j ∈ detected A) =
      ((univ : Finset (Fin 127)).filter fun t => active t = true).map sideEmbedding := by
    rw [← indexed_canonicalSides, filter_map]
    congr 1
    apply filter_congr
    intro t _
    change (labelIndex i ∈ detected (numberedSide t) ∧ labelIndex j ∈ detected (numberedSide t)) ↔ _
    simp only [active, Bool.and_eq_true, mask_correct]
  rw [actual, card_map]
  dsimp only [active]
  revert i j
  decide

private theorem full_pair_of_optimal {S : Finset (Finset Vertex)} (four : S.card = 4)
    (complete : Complete S) {A : Finset Vertex} (mem : A ∈ S) :
    (detected A).card = 2 ∧ Disjoint (detected A) ((S.erase A).biUnion detected) := by
  have all : detected A ∪ (S.erase A).biUnion detected = univ := by
    rw [← biUnion_insert, insert_erase mem]
    exact (complete_iff_union S).mp complete
  have size := card_union_add_card_inter (detected A) ((S.erase A).biUnion detected)
  rw [all] at size
  have other := detected_union_bound (S.erase A)
  rw [card_erase_of_mem mem, four] at other
  have bound := detected_card_le_two A
  have eight : (univ : Finset (Fin 8)).card = 8 := by decide
  rw [eight] at size
  refine ⟨by omega, ?_⟩
  apply Finset.disjoint_iff_inter_eq_empty.mpr
  apply card_eq_zero.mp
  omega

/-- Four tests cover all witnesses exactly when their four detected pairs are disjoint.
In particular each successful pair can be labelled by any cut with that same signature. -/
theorem complete_four_iff_pairing (S : Finset (Finset Vertex)) (four : S.card = 4) :
    Complete S ↔ (∀ A ∈ S, (detected A).card = 2) ∧
      (S : Set (Finset Vertex)).PairwiseDisjoint detected := by
  constructor
  · intro complete
    refine ⟨fun _ mem => (full_pair_of_optimal four complete mem).1, ?_⟩
    intro A hA B hB ne
    have sub : detected B ⊆ (S.erase A).biUnion detected :=
      fun _ h => mem_biUnion.mpr ⟨B, mem_erase.mpr ⟨ne.symm, hB⟩, h⟩
    exact (full_pair_of_optimal four complete hA).2.mono_right sub
  · rintro ⟨two, disjoint⟩
    apply (complete_iff_union S).mpr
    apply (S.biUnion detected).card_eq_iff_eq_univ.mp
    rw [card_biUnion disjoint, sum_congr rfl two]
    simp [four]

end CornerArbitraryCuts
