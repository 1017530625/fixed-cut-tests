import CutSizeIncidence
import SizeCatalogue
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases

/-! Kernel checks for the compact list of four-cut families. -/
namespace CornerArbitraryCuts.SizeRefinement.Catalogue

open Finset CornerLemma SignatureTable

abbrev Profile := ℕ × ℕ × ℕ

def typeOf (j : Fin 9) : Profile :=
  (#[(4,0,0), (3,1,0), (2,2,0), (1,3,0), (0,4,0), (2,0,2), (1,1,2), (0,2,2), (0,0,4)]
    : Array Profile)[j.val]!

def countOf (j : Fin 9) : ℕ := (#[9,72,216,288,144,42,168,168,9] : Array ℕ)[j.val]!

def slot (n : Fin 1116) (p : ℕ) : Fin 127 :=
  ⟨(packed n / 127^p) % 127, Nat.mod_lt _ (by decide)⟩

def cuts (n : Fin 1116) : Finset (Fin 127) := {slot n 0, slot n 1, slot n 2, slot n 3}

def tag (n : Fin 1116) : Fin 9 := ⟨(packed n / 127^4) % 9, Nat.mod_lt _ (by decide)⟩

def counts (n : Fin 1116) (d : ℕ) : ℕ := ((cuts n).filter (fun i => rowSize i = d)).card

def distinctKey (n : Fin 1116) : ℕ := ∑ t ∈ cuts n, 2 ^ t.val

set_option maxRecDepth 12000
set_option maxHeartbeats 16000000

private def grid (N : ℕ) (pos : 0 < N) (b : Fin 36) (r : Fin 31) : Fin N :=
  ⟨(31*b.val + r.val) % N, Nat.mod_lt _ pos⟩

private theorem forall_grid (N : ℕ) (pos : 0 < N) (bound : N ≤ 1116) (P : Fin N → Prop)
    (all : ∀ b r, P (grid N pos b r)) : ∀ i, P i := by
  intro i
  let b : Fin 36 := ⟨i.val / 31, by omega⟩
  let r : Fin 31 := ⟨i.val % 31, Nat.mod_lt _ (by decide)⟩
  have eq : grid N pos b r = i := by
    apply Fin.ext
    change (31 * (i.val / 31) + i.val % 31) % N = i.val
    rw [show 31 * (i.val / 31) + i.val % 31 = i.val by omega, Nat.mod_eq_of_lt i.isLt]
  exact eq ▸ all b r

local macro "check_rows" : tactic => `(tactic|
  (apply forall_grid _ (by decide) (by decide)
   intro b
   fin_cases b <;> decide))

private def maskUnion (n : Fin 1116) : ℕ :=
  (signatureMask (slot n 0) ||| signatureMask (slot n 1)) |||
    (signatureMask (slot n 2) ||| signatureMask (slot n 3))

private def ValidRow (n : Fin 1116) : Prop :=
  (cuts n).card = 4 ∧ maskUnion n = 255 ∧ (counts n 2, counts n 3, counts n 4) = typeOf (tag n)

private instance (n : Fin 1116) : Decidable (ValidRow n) := by unfold ValidRow; infer_instance

private def ValidBlock (b : Fin 36) : Prop := ∀ k : Fin 31, ValidRow (grid 1116 (by decide) b k)

/- Each block is a separate kernel declaration to bound the checker’s working memory. -/
private theorem block0_ok : ValidBlock 0 := by unfold ValidBlock; decide
private theorem block1_ok : ValidBlock 1 := by unfold ValidBlock; decide
private theorem block2_ok : ValidBlock 2 := by unfold ValidBlock; decide
private theorem block3_ok : ValidBlock 3 := by unfold ValidBlock; decide
private theorem block4_ok : ValidBlock 4 := by unfold ValidBlock; decide
private theorem block5_ok : ValidBlock 5 := by unfold ValidBlock; decide
private theorem block6_ok : ValidBlock 6 := by unfold ValidBlock; decide
private theorem block7_ok : ValidBlock 7 := by unfold ValidBlock; decide
private theorem block8_ok : ValidBlock 8 := by unfold ValidBlock; decide
private theorem block9_ok : ValidBlock 9 := by unfold ValidBlock; decide
private theorem block10_ok : ValidBlock 10 := by unfold ValidBlock; decide
private theorem block11_ok : ValidBlock 11 := by unfold ValidBlock; decide
private theorem block12_ok : ValidBlock 12 := by unfold ValidBlock; decide
private theorem block13_ok : ValidBlock 13 := by unfold ValidBlock; decide
private theorem block14_ok : ValidBlock 14 := by unfold ValidBlock; decide
private theorem block15_ok : ValidBlock 15 := by unfold ValidBlock; decide
private theorem block16_ok : ValidBlock 16 := by unfold ValidBlock; decide
private theorem block17_ok : ValidBlock 17 := by unfold ValidBlock; decide
private theorem block18_ok : ValidBlock 18 := by unfold ValidBlock; decide
private theorem block19_ok : ValidBlock 19 := by unfold ValidBlock; decide
private theorem block20_ok : ValidBlock 20 := by unfold ValidBlock; decide
private theorem block21_ok : ValidBlock 21 := by unfold ValidBlock; decide
private theorem block22_ok : ValidBlock 22 := by unfold ValidBlock; decide
private theorem block23_ok : ValidBlock 23 := by unfold ValidBlock; decide
private theorem block24_ok : ValidBlock 24 := by unfold ValidBlock; decide
private theorem block25_ok : ValidBlock 25 := by unfold ValidBlock; decide
private theorem block26_ok : ValidBlock 26 := by unfold ValidBlock; decide
private theorem block27_ok : ValidBlock 27 := by unfold ValidBlock; decide
private theorem block28_ok : ValidBlock 28 := by unfold ValidBlock; decide
private theorem block29_ok : ValidBlock 29 := by unfold ValidBlock; decide
private theorem block30_ok : ValidBlock 30 := by unfold ValidBlock; decide
private theorem block31_ok : ValidBlock 31 := by unfold ValidBlock; decide
private theorem block32_ok : ValidBlock 32 := by unfold ValidBlock; decide
private theorem block33_ok : ValidBlock 33 := by unfold ValidBlock; decide
private theorem block34_ok : ValidBlock 34 := by unfold ValidBlock; decide
private theorem block35_ok : ValidBlock 35 := by unfold ValidBlock; decide

private theorem all_rows : ∀ n : Fin 1116, ValidRow n := by
  apply forall_grid _ (by decide) (by decide)
  intro b
  fin_cases b
  · exact block0_ok
  · exact block1_ok
  · exact block2_ok
  · exact block3_ok
  · exact block4_ok
  · exact block5_ok
  · exact block6_ok
  · exact block7_ok
  · exact block8_ok
  · exact block9_ok
  · exact block10_ok
  · exact block11_ok
  · exact block12_ok
  · exact block13_ok
  · exact block14_ok
  · exact block15_ok
  · exact block16_ok
  · exact block17_ok
  · exact block18_ok
  · exact block19_ok
  · exact block20_ok
  · exact block21_ok
  · exact block22_ok
  · exact block23_ok
  · exact block24_ok
  · exact block25_ok
  · exact block26_ok
  · exact block27_ok
  · exact block28_ok
  · exact block29_ok
  · exact block30_ok
  · exact block31_ok
  · exact block32_ok
  · exact block33_ok
  · exact block34_ok
  · exact block35_ok

theorem cuts_four (n : Fin 1116) : (cuts n).card = 4 := (all_rows n).1

theorem covers_witnesses (n : Fin 1116) (j : Fin 8) :
    (((signatureMask (slot n 0)).testBit j.val || (signatureMask (slot n 1)).testBit j.val) ||
     ((signatureMask (slot n 2)).testBit j.val || (signatureMask (slot n 3)).testBit j.val)) = true := by
  have h := congrArg (fun m : ℕ => m.testBit j.val) (all_rows n).2.1
  have full := (by decide : ∀ i : Fin 8, (255 : ℕ).testBit i.val = true) j
  simpa only [maskUnion, Nat.testBit_or, full] using h

theorem ascending : ∀ n : Fin 1115, distinctKey n.castSucc < distinctKey n.succ := by check_rows

theorem tags_correct (n : Fin 1116) : (counts n 2, counts n 3, counts n 4) = typeOf (tag n) :=
  (all_rows n).2.2

theorem tag_hist : ∀ j : Fin 9,
    ((univ : Finset (Fin 1116)).filter (fun n => tag n = j)).card = countOf j := by decide

theorem typeOf_injective : Function.Injective typeOf := by
  intro i j
  exact (by decide : ∀ i j : Fin 9, typeOf i = typeOf j → i = j) i j

end CornerArbitraryCuts.SizeRefinement.Catalogue