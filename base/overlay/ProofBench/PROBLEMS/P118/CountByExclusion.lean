import ProofBench.PROBLEMS.P118.CutRequirements
import Mathlib.Data.Finset.Powerset

/-! Count unordered fixed-size families by deleting the choices which miss a requirement. -/
namespace CornerCutEnumeration

open Finset

variable {α ι : Type*} [DecidableEq ι]

/-- A family drawn without replacement must hit each requirement in the given list. -/
def families (detect : α → Finset ι) (k : Nat) (available : Finset α)
    (required : List ι) : Finset (Finset α) :=
  (available.powersetCard k).filter fun S => ∀ j ∈ required, ∃ A ∈ S, j ∈ detect A

theorem mem_families {detect : α → Finset ι} {k : Nat} {available : Finset α}
    {required : List ι} {S : Finset α} :
    S ∈ families detect k available required ↔
      S ⊆ available ∧ S.card = k ∧ ∀ j ∈ required, ∃ A ∈ S, j ∈ detect A := by
  simp [families, and_assoc]

/-- Inclusion-exclusion with natural subtraction. The second term counts an actual
subfamily of the first, so every subtraction is exact. -/
def count (detect : α → Finset ι) (k : Nat) : List ι → Finset α → Nat
  | [], available => available.card.descFactorial k / k.factorial
  | j :: js, available => count detect k js available -
      count detect k js (available.filter fun A => j ∉ detect A)

theorem count_eq_card (detect : α → Finset ι) (k : Nat) (required : List ι)
    (available : Finset α) :
    count detect k required available = (families detect k available required).card := by
  induction required generalizing available with
  | nil =>
    simp [families, count, card_powersetCard, Nat.choose_eq_descFactorial_div_factorial]
  | cons j js ih =>
    let X := families detect k available js
    let hit := fun (S : Finset α) => ∃ A ∈ S, j ∈ detect A
    have hgood : X.filter hit = families detect k available (j :: js) := by
      ext S
      simp [X, hit, mem_families, and_comm, and_left_comm]
    have hmiss : (X.filter fun S => ¬hit S) =
        families detect k (available.filter fun A => j ∉ detect A) js := by
      ext S
      simp only [mem_filter, X, hit, mem_families]
      constructor
      · rintro ⟨⟨sub, card, hs⟩, miss⟩
        exact ⟨fun A hA => mem_filter.mpr ⟨sub hA, fun hj => miss ⟨A, hA, hj⟩⟩, card, hs⟩
      · rintro ⟨sub, card, hs⟩
        refine ⟨⟨fun A hA => (mem_filter.mp (sub hA)).1, card, hs⟩, ?_⟩
        rintro ⟨A, hA, hj⟩
        exact (mem_filter.mp (sub hA)).2 hj
    have partition := X.card_filter_add_card_filter_not hit
    rw [hgood, hmiss] at partition
    change _ + _ = (families detect k available js).card at partition
    simp only [count, ih]
    omega

end CornerCutEnumeration
