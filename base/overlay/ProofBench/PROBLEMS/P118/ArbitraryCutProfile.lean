import ProofBench.PROBLEMS.P118.ArbitraryCutCensus

/-! Aggregate counts behind the finite incidence table. Each signature is the actual
set of detected alternating matchings, and multiplicities count canonical proper cuts. -/
namespace CornerArbitraryCuts

open Finset CornerLemma SignatureTable

set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

private def unpackMask (m : Nat) : Finset (Fin 8) :=
  univ.filter fun j => m.testBit j.val

private theorem unpack_correct (i : Fin 127) :
    detected (numberedSide i) = unpackMask (signatureMask i) := by
  ext j
  simp [unpackMask, mask_correct]

private def profile : Multiset (Finset (Fin 8)) := maskHistogram.map unpackMask

private theorem actual_profile : canonicalSides.val.map detected = profile := by
  rw [← indexed_canonicalSides, profile, ← mask_histogram]
  change ((univ : Finset (Fin 127)).val.map sideEmbedding).map detected =
    ((univ : Finset (Fin 127)).val.map signatureMask).map unpackMask
  have eq : detected ∘ sideEmbedding = unpackMask ∘ signatureMask := by
    funext i
    exact unpack_correct i
  simp only [Multiset.map_map, eq]

private theorem filter_profile (p : Finset (Fin 8) → Prop) [DecidablePred p] :
    (canonicalSides.filter fun A => p (detected A)).card = (profile.filter p).card := by
  rw [← actual_profile, Multiset.filter_map, Multiset.card_map]
  rfl

private theorem support_eq : canonicalSides.image detected = profile.toFinset := by
  change (canonicalSides.val.map detected).toFinset = _
  rw [actual_profile]

/-- Among the 127 unordered proper cuts, 79 reject no witness, 48 reject two, and
the useful cuts have 24 different signatures. Each witness is rejected by 12 cuts. -/
theorem signature_census :
    (canonicalSides.filter (fun A => (detected A).card = 0)).card = 79 ∧
    (canonicalSides.filter (fun A => (detected A).card = 2)).card = 48 ∧
    ((canonicalSides.image detected).erase ∅).card = 24 ∧
    ∀ j : Fin 8, (canonicalSides.filter (fun A => j ∈ detected A)).card = 12 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [filter_profile (fun J => J.card = 0)]
    decide
  · rw [filter_profile (fun J => J.card = 2)]
    decide
  · rw [support_eq]
    decide
  · intro j
    rw [filter_profile (fun J => j ∈ J)]
    revert j
    decide

/-- The 24 useful two-witness signatures split equally between multiplicities 1 and 3. -/
theorem signature_multiplicities :
    let useful := (canonicalSides.image detected).erase ∅
    let mult := fun J : Finset (Fin 8) => (canonicalSides.filter fun A => detected A = J).card
    (useful.filter (fun J => mult J = 1)).card = 12 ∧
      (useful.filter (fun J => mult J = 3)).card = 12 := by
  dsimp only
  rw [support_eq]
  have eq : (fun J : Finset (Fin 8) => (canonicalSides.filter fun A => detected A = J).card) =
      fun J => (profile.filter (fun K => K = J)).card := by
    funext J
    exact filter_profile (fun K => K = J)
  simp_rw [show ∀ J : Finset (Fin 8), (canonicalSides.filter fun A => detected A = J).card =
      (profile.filter (fun K => K = J)).card from fun J => congrFun eq J]
  decide

#print axioms signature_census
#print axioms signature_multiplicities

end CornerArbitraryCuts
