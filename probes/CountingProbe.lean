import SizeFamilySeries

namespace ManuscriptCountingCheck

open CornerArbitraryCuts CornerArbitraryCuts.SizeRefinement

#check CornerArbitraryCuts.minimumFamilies_card
#check CornerArbitraryCuts.mem_minimumFamilies_iff_sufficient
#check CornerArbitraryCuts.complete_four_iff_pairing
#check CornerArbitraryCuts.SizeRefinement.pair_multiplicity_by_smaller_side
#check CornerArbitraryCuts.SizeRefinement.size_series_formula
#check CornerArbitraryCuts.SizeRefinement.catalogue_eq
#check CornerArbitraryCuts.SizeRefinement.profile_exhaustive
#check CornerArbitraryCuts.SizeRefinement.size_profile_card
#check CornerArbitraryCuts.SizeRefinement.unlisted_profile_card
#check CornerArbitraryCuts.SizeRefinement.all_three_point_cuts_card
#check CornerArbitraryCuts.SizeRefinement.all_balanced_cuts_card

#print CornerArbitraryCuts.SizeRefinement.smallerSide
#print CornerArbitraryCuts.SizeRefinement.sizeCount
#print CornerArbitraryCuts.SizeRefinement.sizeProfile
#print CornerArbitraryCuts.SizeRefinement.sizeSeries
#print CornerArbitraryCuts.SizeRefinement.Catalogue.typeOf
#print CornerArbitraryCuts.SizeRefinement.Catalogue.countOf

/-- Write the left side entirely in terms of the actual families and their cut-size counts. -/
example {K : Type*} [CommSemiring K] (a b c : K) :
    (∑ S ∈ minimumFamilies, a ^ sizeCount S 2 * b ^ sizeCount S 3 * c ^ sizeCount S 4) =
      9 * (a + 2*b)^4 + 42 * (a + 2*b)^2 * c^2 + 9 * c^4 :=
  size_series_formula a b c

theorem expanded {K : Type*} [CommSemiring K] (a b c : K) :
    sizeSeries a b c = 9*a^4 + 72*a^3*b + 216*a^2*b^2 + 288*a*b^3 + 144*b^4 +
      42*a^2*c^2 + 168*a*b*c^2 + 168*b^2*c^2 + 9*c^4 := by
  rw [size_series_formula]
  ring

theorem evaluation : sizeSeries (1 : ℕ) 1 1 = 1116 := by
  calc
    _ = 9 * (1 + 2*1)^4 + 42 * (1 + 2*1)^2 * 1^2 + 9 * 1^4 := size_series_formula 1 1 1
    _ = 1116 := by decide

theorem evaluation_eq_card : sizeSeries (1 : ℕ) 1 1 = minimumFamilies.card :=
  evaluation.trans minimumFamilies_card.symm

#check expanded
#check evaluation
#check evaluation_eq_card
#print axioms CornerArbitraryCuts.minimumFamilies_card
#print axioms CornerArbitraryCuts.mem_minimumFamilies_iff_sufficient
#print axioms CornerArbitraryCuts.complete_four_iff_pairing
#print axioms CornerArbitraryCuts.SizeRefinement.pair_multiplicity_by_smaller_side
#print axioms CornerArbitraryCuts.SizeRefinement.size_series_formula
#print axioms CornerArbitraryCuts.SizeRefinement.catalogue_eq
#print axioms CornerArbitraryCuts.SizeRefinement.profile_exhaustive
#print axioms CornerArbitraryCuts.SizeRefinement.size_profile_card
#print axioms CornerArbitraryCuts.SizeRefinement.unlisted_profile_card
#print axioms CornerArbitraryCuts.SizeRefinement.all_three_point_cuts_card
#print axioms CornerArbitraryCuts.SizeRefinement.all_balanced_cuts_card
#print axioms ManuscriptCountingCheck.expanded
#print axioms ManuscriptCountingCheck.evaluation
#print axioms ManuscriptCountingCheck.evaluation_eq_card

end ManuscriptCountingCheck
