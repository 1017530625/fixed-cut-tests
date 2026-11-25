import SizeFamilyCertificate
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

/-! Exact coefficients and generating polynomial for actual minimum families of cube cuts. -/
namespace CornerArbitraryCuts.SizeRefinement

open Finset CornerLemma SignatureTable Catalogue

set_option maxRecDepth 20000
set_option maxHeartbeats 1500000

/-- The family of actual canonical sides represented by one candidate tuple. -/
def represented (n : Fin 1116) : Finset (Finset Vertex) := (cuts n).map sideEmbedding

private theorem cuts_injective : Function.Injective cuts := by
  have strict : StrictMono distinctKey := Fin.strictMono_iff_lt_succ.mpr ascending
  intro n m heq
  apply strict.injective
  exact congrArg (fun S : Finset (Fin 127) => ∑ t ∈ S, 2^t.val) heq

def familyEmbedding : Fin 1116 ↪ Finset (Finset Vertex) where
  toFun := represented
  inj' := fun _ _ heq => cuts_injective (map_injective sideEmbedding heq)

private theorem represented_mem (n : Fin 1116) : represented n ∈ minimumFamilies := by
  apply mem_minimumFamilies.mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [← indexed_canonicalSides]
    intro A h
    obtain ⟨i, _, rfl⟩ := mem_map.mp h
    exact mem_map.mpr ⟨i, mem_univ _, rfl⟩
  · simpa only [represented, card_map] using cuts_four n
  · intro j
    have hit (p : ℕ) (inCuts : slot n p ∈ cuts n)
        (b : (signatureMask (slot n p)).testBit j.val = true) :
        ∃ A ∈ represented n, j ∈ detected A :=
      ⟨numberedSide (slot n p), mem_map.mpr ⟨slot n p, inCuts, rfl⟩, (mask_correct _ _).mpr b⟩
    have covered := covers_witnesses n j
    simp only [Bool.or_eq_true] at covered
    rcases covered with (h | h) | (h | h)
    · exact hit 0 (by simp [cuts]) h
    · exact hit 1 (by simp [cuts]) h
    · exact hit 2 (by simp [cuts]) h
    · exact hit 3 (by simp [cuts]) h

/-- The candidate list is precisely the mathematical set of minimum complete cut families. -/
theorem catalogue_eq : univ.map familyEmbedding = minimumFamilies := by
  apply eq_of_subset_of_card_le
  · intro S hs
    obtain ⟨n, _, rfl⟩ := mem_map.mp hs
    exact represented_mem n
  · simp [minimumFamilies_card]

/-- Number of members in an actual family that have d corners on their smaller side. -/
def sizeCount (S : Finset (Finset Vertex)) (d : ℕ) : ℕ :=
  (S.filter fun A => smallerSide A = d).card

def sizeProfile (S : Finset (Finset Vertex)) : Profile := (sizeCount S 2, sizeCount S 3, sizeCount S 4)

private theorem counted (n : Fin 1116) (d : ℕ) : sizeCount (familyEmbedding n) d = counts n d := by
  change (((cuts n).map sideEmbedding).filter (fun A => smallerSide A = d)).card = _
  rw [filter_map, card_map]
  apply congrArg Finset.card
  apply filter_congr
  intro i _
  change (smallerSide (numberedSide i) = d ↔ rowSize i = d)
  rw [rowSize_correct]

theorem profile_agrees (n : Fin 1116) : sizeProfile (familyEmbedding n) = typeOf (tag n) := by
  simpa only [sizeProfile, counted] using tags_correct n

/-- These nine rows exhaust all profiles of actual four-cut complete families. -/
theorem profile_exhaustive {S : Finset (Finset Vertex)} (h : S ∈ minimumFamilies) :
    ∃ j : Fin 9, sizeProfile S = typeOf j := by
  rw [← catalogue_eq] at h
  obtain ⟨n, _, rfl⟩ := mem_map.mp h
  exact ⟨tag n, profile_agrees n⟩

theorem size_profile_card (j : Fin 9) :
    (minimumFamilies.filter (fun S => sizeProfile S = typeOf j)).card = countOf j := by
  rw [← catalogue_eq, filter_map, card_map]
  calc
    _ = ((univ : Finset (Fin 1116)).filter (fun n => tag n = j)).card := by
      apply congrArg Finset.card
      apply filter_congr
      intro n _
      change sizeProfile (familyEmbedding n) = typeOf j ↔ tag n = j
      rw [profile_agrees]
      exact typeOf_injective.eq_iff
    _ = _ := tag_hist j

theorem unlisted_profile_card (p : Profile) (absent : ∀ j : Fin 9, p ≠ typeOf j) :
    (minimumFamilies.filter (fun S => sizeProfile S = p)).card = 0 := by
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro S hs e
  obtain ⟨j, hj⟩ := profile_exhaustive hs
  exact absent j (e.symm.trans hj)

/-- Four cuts whose smaller sides have three corners. -/
theorem four_three_point_cuts_card :
    (minimumFamilies.filter (fun S => sizeProfile S = (0,4,0))).card = 144 :=
  size_profile_card (4 : Fin 9)

/-- Four balanced cuts. -/
theorem four_balanced_cuts_card :
    (minimumFamilies.filter (fun S => sizeProfile S = (0,0,4))).card = 9 :=
  size_profile_card (8 : Fin 9)

private theorem all_have_size_iff (S : Finset (Finset Vertex)) (four : S.card = 4) (d : ℕ) :
    (∀ A ∈ S, smallerSide A = d) ↔ sizeCount S d = 4 := by
  change _ ↔ (S.filter _).card = 4
  constructor
  · intro h
    rw [filter_eq_self.mpr h, four]
  · intro hc
    have eq : (S.filter (fun A => smallerSide A = d)) = S :=
      eq_of_subset_of_card_le (filter_subset _ _) (by omega)
    intro A ha
    have hf : A ∈ S.filter (fun B => smallerSide B = d) := by rwa [eq]
    exact (mem_filter.mp hf).2

theorem all_three_point_cuts_card :
    (minimumFamilies.filter (fun S => ∀ A ∈ S, smallerSide A = 3)).card = 144 := by
  rw [← four_three_point_cuts_card]
  apply congrArg Finset.card
  apply filter_congr
  intro S hs
  rw [all_have_size_iff S (mem_minimumFamilies.mp hs).2.1 3]
  change (sizeProfile S).2.1 = 4 ↔ sizeProfile S = (0,4,0)
  obtain ⟨j, hj⟩ := profile_exhaustive hs
  rw [hj]
  exact (by decide : ∀ j : Fin 9, (typeOf j).2.1 = 4 ↔ typeOf j = (0,4,0)) j

theorem all_balanced_cuts_card :
    (minimumFamilies.filter (fun S => ∀ A ∈ S, smallerSide A = 4)).card = 9 := by
  rw [← four_balanced_cuts_card]
  apply congrArg Finset.card
  apply filter_congr
  intro S hs
  rw [all_have_size_iff S (mem_minimumFamilies.mp hs).2.1 4]
  change (sizeProfile S).2.2 = 4 ↔ sizeProfile S = (0,0,4)
  obtain ⟨j, hj⟩ := profile_exhaustive hs
  rw [hj]
  exact (by decide : ∀ j : Fin 9, (typeOf j).2.2 = 4 ↔ typeOf j = (0,0,4)) j

private def monomial {K : Type*} [CommSemiring K] (a b c : K) (p : Profile) : K :=
  a^p.1 * b^p.2.1 * c^p.2.2

/-- Each distinct, unordered complete family contributes once. The three exponents
are obtained by filtering actual cuts on their smaller-side cardinalities. -/
def sizeSeries {K : Type*} [CommSemiring K] (a b c : K) : K :=
  ∑ S ∈ minimumFamilies, monomial a b c (sizeProfile S)

theorem size_series_formula {K : Type*} [CommSemiring K] (a b c : K) :
    sizeSeries a b c = 9 * (a + 2*b)^4 + 42 * (a + 2*b)^2 * c^2 + 9 * c^4 := by
  rw [sizeSeries, ← catalogue_eq, sum_map]
  simp only [profile_agrees]
  calc
    _ = ∑ j : Fin 9, ∑ n ∈ (univ : Finset (Fin 1116)).filter (fun n => tag n = j),
          monomial a b c (typeOf j) :=
      (sum_fiberwise' univ tag (fun j => monomial a b c (typeOf j))).symm
    _ = ∑ j : Fin 9, (countOf j : K) * monomial a b c (typeOf j) := by
      apply sum_congr rfl
      intro j _
      simp only [sum_const, tag_hist, nsmul_eq_mul]
    _ = _ := by
      simp [Fin.sum_univ_succ, countOf, typeOf, monomial]
      ring

end CornerArbitraryCuts.SizeRefinement