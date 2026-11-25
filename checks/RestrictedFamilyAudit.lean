import ProofBench.PROBLEMS.P118.ArbitraryCutCensus

/-! Enumerate two restrictions of the genuine minimum-family census through
eight-witness inclusion-exclusion and restricted 127-cut signature histograms. -/
namespace RestrictedFamilyAudit

open Finset CornerLemma CornerArbitraryCuts CornerCutEnumeration CornerArbitraryCuts.SignatureTable

def smaller (A : Finset Vertex) : ℕ := min A.card (8 - A.card)

/-- These are actual four-element families of canonical unordered cuts. -/
abbrev restricted (d : ℕ) :=
  minimumFamilies.filter fun S => ∀ A ∈ S, smaller A = d

private def candidates (d : ℕ) := canonicalSides.filter fun A => smaller A = d

private theorem restricted_as_families (d : ℕ) :
    restricted d = families detected 4 (candidates d) (List.finRange 8) := by
  ext S
  simp only [restricted, minimumFamilies, mem_filter, mem_families]
  constructor
  · rintro ⟨⟨sub,card,hits⟩,sizes⟩
    exact ⟨fun A ha => mem_filter.mpr ⟨sub ha, sizes A ha⟩,card,hits⟩
  · rintro ⟨sub,card,hits⟩
    exact ⟨⟨fun A ha => (mem_filter.mp (sub ha)).1,card,hits⟩,
      fun A ha => (mem_filter.mp (sub ha)).2⟩

private inductive Kind | three | balanced

private def Kind.size : Kind → ℕ
  | .three => 3
  | .balanced => 4

private def indices (p : Kind) : Finset (Fin 127) :=
  univ.filter fun i => smaller (numberedSide i) = p.size

/-- Numerical signature data for only the two shapes, including undetecting cuts.
Every row/cut is checked below using its actual eight cube vertices. -/
private def hist : Kind → Multiset ℕ
  | .three => Multiset.replicate 32 0 +
      (([5,5,10,10,18,18,20,20,33,33,40,40,65,65,72,72,80,80,130,130,132,132,160,160] : List ℕ) : Multiset ℕ)
  | .balanced => Multiset.replicate 23 0 +
      (([6,9,17,24,34,36,66,68,96,129,136,144] : List ℕ) : Multiset ℕ)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
private theorem hist_correct (p : Kind) :
    (indices p).val.map signatureMask = hist p := by
  cases p <;> decide

private def clear (js : List (Fin 8)) (m : ℕ) : Prop := ∀ j ∈ js, m.testBit j.val = false

private instance (js : List (Fin 8)) : DecidablePred (clear js) := by
  intro m
  unfold clear
  infer_instance

private def available (p : Kind) (js : List (Fin 8)) :=
  canonicalSides.filter fun A => smaller A = p.size ∧ ∀ j ∈ js, j ∉ detected A

private theorem available_cons (p : Kind) (j : Fin 8) (js : List (Fin 8)) :
    (available p js).filter (fun A => j ∉ detected A) = available p (j :: js) := by
  ext A
  simp [available, and_left_comm, and_comm]

private theorem available_map (p : Kind) (js : List (Fin 8)) :
    available p js = ((indices p).filter fun i => clear js (signatureMask i)).map sideEmbedding := by
  rw [available, ← indexed_canonicalSides, filter_map]
  apply congrArg (Finset.map sideEmbedding)
  ext i
  simp only [indices, mem_filter, mem_univ, true_and]
  change (smaller (numberedSide i) = p.size ∧ ∀ j ∈ js, j ∉ detected (numberedSide i)) ↔ _
  simp [clear, mask_correct]

private def remaining (p : Kind) (js : List (Fin 8)) : ℕ :=
  ((hist p).filter (clear js)).card

private theorem available_card (p : Kind) (js : List (Fin 8)) :
    (available p js).card = remaining p js := by
  rw [available_map, card_map, remaining, ← hist_correct, Multiset.filter_map, Multiset.card_map]
  rfl

private def evaluate (p : Kind) : List (Fin 8) → List (Fin 8) → ℕ
  | [], excluded => (remaining p excluded).descFactorial 4 / (4 : ℕ).factorial
  | j :: js, excluded => evaluate p js excluded - evaluate p js (j :: excluded)

private theorem count_evaluate (p : Kind) (required excluded : List (Fin 8)) :
    count detected 4 required (available p excluded) = evaluate p required excluded := by
  induction required generalizing excluded with
  | nil => simp only [count, evaluate, available_card]
  | cons j js ih => rw [count, evaluate, available_cons, ih, ih]

private theorem actual_count (p : Kind) :
    (restricted p.size).card = evaluate p (List.finRange 8) [] := by
  have initial : available p [] = candidates p.size := by simp [available, candidates]
  rw [restricted_as_families, ← count_eq_card, ← initial, count_evaluate]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
/-- Exactly nine minimum families have four balanced (4+4) cuts. -/
theorem all_balanced :
    (minimumFamilies.filter (fun S => ∀ A ∈ S, min A.card (8 - A.card) = 4)).card = 9 := by
  change (restricted Kind.balanced.size).card = 9
  rw [actual_count]
  decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
/-- Exactly 144 minimum families use only 3+5 cuts. -/
theorem all_three_five :
    (minimumFamilies.filter (fun S => ∀ A ∈ S, min A.card (8 - A.card) = 3)).card = 144 := by
  change (restricted Kind.three.size).card = 144
  rw [actual_count]
  decide

end RestrictedFamilyAudit
