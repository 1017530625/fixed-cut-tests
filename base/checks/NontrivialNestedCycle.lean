import ProofBench.Research.KeyCornerLemma
import ProofBench.Research.FlowerCycle24

/-! A test of the other proof branch with three distinct order-two separations. -/
namespace CornerSection.NestedCycle24
open Finset
abbrev host := Cycle24.host

private def ends (i : Fin 3) : Fin 24 × Fin 24 :=
  if i = 0 then (0,12) else if i = 1 then (8,16) else (4,20)

private def arc (i : Fin 3) (b : Bool) : Finset (Fin 24) :=
  univ.filter fun x =>
    let (l,u) := ends i
    if b then x ≤ l ∨ u ≤ x else l ≤ x ∧ x ≤ u

set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

private theorem cover : ∀ i, arc i false ∪ arc i true = univ := by decide
private theorem no_edges : ∀ (i : Fin 3) (x y : Fin 24), host.Adj x y →
    x ∈ arc i false \ arc i true → y ∉ arc i true \ arc i false := by decide

def D (i : Fin 3) : host.Separation where
  A := arc i false
  B := arc i true
  union_eq := cover i
  no_edge_across := fun {x y} => no_edges i x y

private instance (s t : host.Separation) : Decidable (Cross s t) := by
  unfold Cross Nested OrientedBelow
  infer_instance

theorem crossing_pattern : ∀ (i j : Fin 3), Cross (D i) (D j) ↔
    (i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0) := by decide

theorem literal_nesting : (D 1).A ⊆ (D 2).A ∧ (D 2).B ⊆ (D 1).B := by decide
theorem nested : Nested (D 1) (D 2) := ⟨false,false,literal_nesting⟩
theorem orders : ∀ i, (D i).order = 2 := by decide
theorem equitable : Equitable D 2 := by unfold Equitable; decide
theorem criss : CrissCompatible D (2 * 0 + 2) := by unfold CrissCompatible; decide

/-- The two different crossers agree on nonempty links of the first separator. -/
theorem partitions : ∀ j : Fin 3, j ≠ 0 →
    centre (D 0) (D j) = ∅ ∧ link (D 0) (D j) false = {12} ∧
        link (D 0) (D j) true = {0} := by decide

theorem via_nested : UniformlyCrossing D := nested_triple_uniform D 2 equitable nested
theorem via_key : UniformlyCrossing D := key_lemma_4_14 D 0 2 Cycle24.unbreakable orders equitable criss

#print axioms crossing_pattern
#print axioms literal_nesting
#print axioms partitions
#print axioms via_nested
#print axioms via_key
end CornerSection.NestedCycle24
