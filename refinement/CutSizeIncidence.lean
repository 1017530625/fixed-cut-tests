import ProofBench.Research.WitnessPairing

/-! Actual cut multiplicities indexed by the cardinality of the smaller side. -/
namespace CornerArbitraryCuts.SizeRefinement

open Finset CornerLemma SignatureTable

/-- The smaller part of an unordered proper bipartition of the eight cube corners. -/
def smallerSide (A : Finset Vertex) : ℕ := min A.card (8 - A.card)

theorem smallerSide_le (A : Finset Vertex) : smallerSide A ≤ 4 := by
  unfold smallerSide
  omega

/-- This table is checked against the 127 actual numbered sides below. -/
def rowSize (i : Fin 127) : ℕ :=
  (#[
    1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, 1, 2, 2, 3, 2, 3, 3, 4, 2,
    3, 3, 4, 3, 4, 4, 3, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 3, 2,
    3, 3, 4, 3, 4, 4, 3, 3, 4, 4, 3, 4, 3, 3, 2, 1, 2, 2, 3, 2, 3, 3, 4, 2,
    3, 3, 4, 3, 4, 4, 3, 2, 3, 3, 4, 3, 4, 4, 3, 3, 4, 4, 3, 4, 3, 3, 2, 2,
    3, 3, 4, 3, 4, 4, 3, 3, 4, 4, 3, 4, 3, 3, 2, 3, 4, 4, 3, 4, 3, 3, 2, 4,
    3, 3, 2, 3, 2, 2, 1 ] : Array ℕ)[i.val]!

set_option maxRecDepth 10000 in
theorem rowSize_correct : ∀ i : Fin 127, smallerSide (numberedSide i) = rowSize i := by decide

/-- Expected multiplicity for witness distance h and cut smaller-side size d. -/
def multiplicity (h d : ℕ) : ℕ :=
  if h = 1 then (if d = 2 then 1 else if d = 3 then 2 else 0)
  else if h = 2 ∧ d = 4 then 1 else 0

private def admissible (i j : Fin 8) (d : ℕ) (t : Fin 127) : Prop :=
  (signatureMask t).testBit (labelIndex i).val = true ∧
  (signatureMask t).testBit (labelIndex j).val = true ∧ rowSize t = d

private instance (i j : Fin 8) (d : ℕ) (t : Fin 127) : Decidable (admissible i j d t) := by
  unfold admissible
  infer_instance

set_option maxRecDepth 40000 in
set_option maxHeartbeats 6000000 in
private theorem incidence_table : ∀ i j : Fin 8, i ≠ j → ∀ d : Fin 5,
    (univ.filter (admissible i j d.val)).card = multiplicity (labelDistance i j) d.val := by
  decide

set_option maxRecDepth 18000 in
/-- Exact multiplicity among the actual canonical cut sides for every natural d.
Distinct witnesses at distance one admit one cut of smaller size two and two
of size three. Distance two admits a single balanced cut. -/
theorem pair_multiplicity_by_smaller_side (i j : Fin 8) (ne : i ≠ j) (d : ℕ) :
    (canonicalSides.filter fun A =>
      labelIndex i ∈ detected A ∧ labelIndex j ∈ detected A ∧ smallerSide A = d).card =
      multiplicity (labelDistance i j) d := by
  by_cases bound : d < 5
  · have transfer :
        (canonicalSides.filter fun A =>
          labelIndex i ∈ detected A ∧ labelIndex j ∈ detected A ∧ smallerSide A = d) =
        ((univ : Finset (Fin 127)).filter (admissible i j d)).map sideEmbedding := by
      rw [← indexed_canonicalSides, filter_map]
      apply congrArg (Finset.map sideEmbedding)
      apply filter_congr
      intro t _
      change (labelIndex i ∈ detected (numberedSide t) ∧ labelIndex j ∈ detected (numberedSide t) ∧
        smallerSide (numberedSide t) = d) ↔ admissible i j d t
      simp only [admissible, mask_correct, rowSize_correct]
    rw [transfer, card_map]
    exact incidence_table i j ne ⟨d,bound⟩
  · have none : (canonicalSides.filter fun A =>
        labelIndex i ∈ detected A ∧ labelIndex j ∈ detected A ∧ smallerSide A = d) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro A _ hit
      have small := smallerSide_le A
      omega
    rw [none, card_empty]
    simp [multiplicity, show d ≠ 2 by omega, show d ≠ 3 by omega, show d ≠ 4 by omega]

end CornerArbitraryCuts.SizeRefinement
