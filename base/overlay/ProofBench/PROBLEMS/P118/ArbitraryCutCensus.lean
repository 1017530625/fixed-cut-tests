import ProofBench.PROBLEMS.P118.ArbitraryCutBounds
import ProofBench.PROBLEMS.P118.ArbitraryCutTable
import ProofBench.PROBLEMS.P118.CountByExclusion

/-! Exact cardinalities of actual finite sets of unordered families of unordered proper cuts.
The count uses inclusion-exclusion over witnesses, not a powerset enumeration of the cuts. -/
namespace CornerArbitraryCuts

open Finset CornerLemma CornerCutEnumeration SignatureTable

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

theorem canonical_orientation (A : Finset Vertex) (h : A.Nonempty) (hc : Aᶜ.Nonempty) :
    (A ∈ canonicalSides ∧ Aᶜ ∉ canonicalSides) ∨
      (Aᶜ ∈ canonicalSides ∧ A ∉ canonicalSides) := by
  by_cases hv : (fun _ : Fin 3 => false) ∈ A <;> simp [canonicalSides, h, hc, hv]

theorem indexed_canonicalSides : univ.map sideEmbedding = canonicalSides := by
  apply eq_of_subset_of_card_le
  · intro A h
    obtain ⟨i, _, rfl⟩ := mem_map.mp h
    exact mem_filter.mpr ⟨mem_univ _, canonical_numberedSide i⟩
  · simp [canonicalSides_card]

private def available (excluded : List (Fin 8)) : Finset (Finset Vertex) :=
  canonicalSides.filter fun A => ∀ j ∈ excluded, j ∉ detected A

private theorem available_cons (j : Fin 8) (excluded : List (Fin 8)) :
    (available excluded).filter (fun A => j ∉ detected A) = available (j :: excluded) := by
  ext A
  simp [available, and_left_comm, and_comm]

private def maskClear (excluded : List (Fin 8)) (m : Nat) : Prop :=
  ∀ j ∈ excluded, m.testBit j.val = false

private instance clearDecidable (excluded : List (Fin 8)) : DecidablePred (maskClear excluded) :=
  fun m => by unfold maskClear; infer_instance

private theorem available_eq_map (excluded : List (Fin 8)) :
    available excluded =
      ((univ : Finset (Fin 127)).filter fun i => maskClear excluded (signatureMask i)).map
        sideEmbedding := by
  rw [available, ← indexed_canonicalSides, filter_map]
  congr 1
  apply filter_congr
  intro i _
  change (∀ j ∈ excluded, j ∉ detected (numberedSide i)) ↔ maskClear excluded (signatureMask i)
  simp [mask_correct, maskClear]

private def survivorCount (excluded : List (Fin 8)) : Nat :=
  (maskHistogram.filter (maskClear excluded)).card

private theorem available_card (excluded : List (Fin 8)) :
    (available excluded).card = survivorCount excluded := by
  rw [available_eq_map, card_map, survivorCount, ← mask_histogram, Multiset.filter_map,
    Multiset.card_map]
  rfl

private def evaluate (k : Nat) : List (Fin 8) → List (Fin 8) → Nat
  | [], excluded => (survivorCount excluded).descFactorial k / k.factorial
  | j :: js, excluded => evaluate k js excluded - evaluate k js (j :: excluded)

private theorem count_evaluate (k : Nat) (required excluded : List (Fin 8)) :
    CornerCutEnumeration.count detected k required (available excluded) =
      evaluate k required excluded := by
  induction required generalizing excluded with
  | nil => simp only [CornerCutEnumeration.count, evaluate, available_card]
  | cons j js ih => rw [CornerCutEnumeration.count, evaluate, available_cons, ih, ih]

private theorem count_actual (k : Nat) (required : List (Fin 8)) :
    (families detected k canonicalSides required).card = evaluate k required [] := by
  have ha : available [] = canonicalSides := by simp [available]
  rw [← count_eq_card, ← ha, count_evaluate]

/-- Each element is an unordered set of four distinct unordered proper corner cuts. -/
def minimumFamilies : Finset (Finset (Finset Vertex)) :=
  families detected 4 canonicalSides (List.finRange 8)

theorem mem_minimumFamilies {S : Finset (Finset Vertex)} :
    S ∈ minimumFamilies ↔ S ⊆ canonicalSides ∧ S.card = 4 ∧ Complete S := by
  simp [minimumFamilies, mem_families, Complete]

theorem minimumFamilies_card : minimumFamilies.card = 1116 := by
  rw [minimumFamilies, count_actual]
  decide

/-- The two witnesses are fixed by the observed six-ring. All 127 canonical cube cuts
remain eligible for selection; the two elements of each family are unordered. -/
def ringMinimumFamilies (q : Fin 4) : Finset (Finset (Finset Vertex)) :=
  families detected 2 canonicalSides [CoverAware.index q false, CoverAware.index q true]

theorem mem_ringMinimumFamilies {q : Fin 4} {S : Finset (Finset Vertex)} :
    S ∈ ringMinimumFamilies q ↔ S ⊆ canonicalSides ∧ S.card = 2 ∧ CompleteAt q S := by
  rw [ringMinimumFamilies, mem_families]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨h, hs, ha, hb⟩
    exact ⟨h, hs, fun b => by cases b <;> assumption⟩
  · rintro ⟨h, hs, hab⟩
    exact ⟨h, hs, hab false, hab true⟩

theorem ringMinimumFamilies_card (q : Fin 4) : (ringMinimumFamilies q).card = 144 := by
  rw [ringMinimumFamilies, count_actual]
  revert q
  decide

#print axioms canonical_orientation
#print axioms indexed_canonicalSides
#print axioms mem_minimumFamilies
#print axioms minimumFamilies_card
#print axioms mem_ringMinimumFamilies
#print axioms ringMinimumFamilies_card

end CornerArbitraryCuts
