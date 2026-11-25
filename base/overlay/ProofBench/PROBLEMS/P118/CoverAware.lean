import ProofBench.PROBLEMS.P118.CutLowerBound
import Mathlib.Data.Fintype.Powerset

/-! The arithmetic certificates specialize the six existing cover branches of
CubeTransversals to the observed cover and to its own two matchings. -/

namespace CoverAware
open Finset CornerLemma
open CornerCutLowerBound
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
private def triple {α : Type} (a b c : α) (i : Fin 3) : α :=
  if i.val = 0 then a else if i.val = 1 then b else c
private abbrev v0 : Vertex := triple false false false
private abbrev v1 : Vertex := triple false false true
private abbrev v2 : Vertex := triple false true false
private abbrev v3 : Vertex := triple false true true
private abbrev v4 : Vertex := triple true false false
private abbrev v5 : Vertex := triple true false true
private abbrev v6 : Vertex := triple true true false
private abbrev v7 : Vertex := triple true true true
private abbrev f00x : Face := triple (some false) (some false) none
private abbrev f01x : Face := triple (some false) (some true) none
private abbrev f0x0 : Face := triple (some false) none (some false)
private abbrev f0x1 : Face := triple (some false) none (some true)
private abbrev f0xx : Face := triple (some false) none none
private abbrev f10x : Face := triple (some true) (some false) none
private abbrev f11x : Face := triple (some true) (some true) none
private abbrev f1x0 : Face := triple (some true) none (some false)
private abbrev f1x1 : Face := triple (some true) none (some true)
private abbrev f1xx : Face := triple (some true) none none
private abbrev fx00 : Face := triple none (some false) (some false)
private abbrev fx01 : Face := triple none (some false) (some true)
private abbrev fx0x : Face := triple none (some false) none
private abbrev fx10 : Face := triple none (some true) (some false)
private abbrev fx11 : Face := triple none (some true) (some true)
private abbrev fx1x : Face := triple none (some true) none
private abbrev fxx0 : Face := triple none none (some false)
private abbrev fxx1 : Face := triple none none (some true)
private abbrev fxxx : Face := fun _ => none
private theorem dimension1 : ∀ f : Face, dim f = 1 → f = f00x ∨ f = f01x ∨ f = f0x0 ∨ f = f0x1 ∨ f = f10x ∨ f = f11x ∨ f = f1x0 ∨ f = f1x1 ∨ f = fx00 ∨ f = fx01 ∨ f = fx10 ∨ f = fx11 := by decide
private theorem dimension2 : ∀ f : Face, dim f = 2 → f = f0xx ∨ f = f1xx ∨ f = fx0x ∨ f = fx1x ∨ f = fxx0 ∨ f = fxx1 := by decide
private theorem classify (R : Finset Vertex) (h : CubeCertificate.EdgeCover R) :
    (v0 ∈ R ∧ v3 ∈ R ∧ v5 ∈ R ∧ v6 ∈ R) ∨
    (v1 ∈ R ∧ v2 ∈ R ∧ v4 ∈ R ∧ v7 ∈ R) ∨
    (v1 ∈ R ∧ v2 ∈ R ∧ v3 ∈ R ∧ v4 ∈ R ∧ v5 ∈ R ∧ v6 ∈ R) ∨
    (v0 ∈ R ∧ v2 ∈ R ∧ v3 ∈ R ∧ v4 ∈ R ∧ v5 ∈ R ∧ v7 ∈ R) ∨
    (v0 ∈ R ∧ v1 ∈ R ∧ v3 ∈ R ∧ v4 ∈ R ∧ v6 ∈ R ∧ v7 ∈ R) ∨
    (v0 ∈ R ∧ v1 ∈ R ∧ v2 ∈ R ∧ v5 ∈ R ∧ v6 ∈ R ∧ v7 ∈ R) := by
  have edge01 := h v0 v1 (by decide)
  have edge02 := h v0 v2 (by decide)
  have edge04 := h v0 v4 (by decide)
  have edge13 := h v1 v3 (by decide)
  have edge15 := h v1 v5 (by decide)
  have edge23 := h v2 v3 (by decide)
  have edge26 := h v2 v6 (by decide)
  have edge37 := h v3 v7 (by decide)
  have edge45 := h v4 v5 (by decide)
  have edge46 := h v4 v6 (by decide)
  have edge57 := h v5 v7 (by decide)
  have edge67 := h v6 v7 (by decide)
  grind only
private theorem coord0 (lam : Face → Nat) :
    cutValue lam (univ.filter fun (v : Vertex) => v (0 : Fin 3) = false) =
      lam fx00 + (lam fx01 + (lam fx0x + (lam fx10 + (lam fx11 + (lam fx1x + (lam fxx0 + (lam fxx1 + (lam fxxx)))))))) := by
  unfold cutValue
  calc
    _ = (([fx00, fx01, fx0x, fx10, fx11, fx1x, fxx0, fxx1, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem coord1 (lam : Face → Nat) :
    cutValue lam (univ.filter fun (v : Vertex) => v (1 : Fin 3) = false) =
      lam f0x0 + (lam f0x1 + (lam f0xx + (lam f1x0 + (lam f1x1 + (lam f1xx + (lam fxx0 + (lam fxx1 + (lam fxxx)))))))) := by
  unfold cutValue
  calc
    _ = (([f0x0, f0x1, f0xx, f1x0, f1x1, f1xx, fxx0, fxx1, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem coord2 (lam : Face → Nat) :
    cutValue lam (univ.filter fun (v : Vertex) => v (2 : Fin 3) = false) =
      lam f00x + (lam f01x + (lam f0xx + (lam f10x + (lam f11x + (lam f1xx + (lam fx0x + (lam fx1x + (lam fxxx)))))))) := by
  unfold cutValue
  calc
    _ = (([f00x, f01x, f0xx, f10x, f11x, f1xx, fx0x, fx1x, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem atomic0 (lam : Face → Nat) :
    cutValue lam ({v0}) =
      lam f00x + (lam f0x0 + (lam f0xx + (lam fx00 + (lam fx0x + (lam fxx0 + (lam fxxx)))))) := by
  unfold cutValue
  calc
    _ = (([f00x, f0x0, f0xx, fx00, fx0x, fxx0, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem atomic1 (lam : Face → Nat) :
    cutValue lam ({v1}) =
      lam f00x + (lam f0x1 + (lam f0xx + (lam fx01 + (lam fx0x + (lam fxx1 + (lam fxxx)))))) := by
  unfold cutValue
  calc
    _ = (([f00x, f0x1, f0xx, fx01, fx0x, fxx1, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem atomic2 (lam : Face → Nat) :
    cutValue lam ({v2}) =
      lam f01x + (lam f0x0 + (lam f0xx + (lam fx10 + (lam fx1x + (lam fxx0 + (lam fxxx)))))) := by
  unfold cutValue
  calc
    _ = (([f01x, f0x0, f0xx, fx10, fx1x, fxx0, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem atomic3 (lam : Face → Nat) :
    cutValue lam ({v3}) =
      lam f01x + (lam f0x1 + (lam f0xx + (lam fx11 + (lam fx1x + (lam fxx1 + (lam fxxx)))))) := by
  unfold cutValue
  calc
    _ = (([f01x, f0x1, f0xx, fx11, fx1x, fxx1, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem atomic4 (lam : Face → Nat) :
    cutValue lam ({v4}) =
      lam f10x + (lam f1x0 + (lam f1xx + (lam fx00 + (lam fx0x + (lam fxx0 + (lam fxxx)))))) := by
  unfold cutValue
  calc
    _ = (([f10x, f1x0, f1xx, fx00, fx0x, fxx0, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem atomic5 (lam : Face → Nat) :
    cutValue lam ({v5}) =
      lam f10x + (lam f1x1 + (lam f1xx + (lam fx01 + (lam fx0x + (lam fxx1 + (lam fxxx)))))) := by
  unfold cutValue
  calc
    _ = (([f10x, f1x1, f1xx, fx01, fx0x, fxx1, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem atomic6 (lam : Face → Nat) :
    cutValue lam ({v6}) =
      lam f11x + (lam f1x0 + (lam f1xx + (lam fx10 + (lam fx1x + (lam fxx0 + (lam fxxx)))))) := by
  unfold cutValue
  calc
    _ = (([f11x, f1x0, f1xx, fx10, fx1x, fxx0, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem atomic7 (lam : Face → Nat) :
    cutValue lam ({v7}) =
      lam f11x + (lam f1x1 + (lam f1xx + (lam fx11 + (lam fx1x + (lam fxx1 + (lam fxxx)))))) := by
  unfold cutValue
  calc
    _ = (([f11x, f1x1, f1xx, fx11, fx1x, fxx1, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem pair01 (lam : Face → Nat) :
    cutValue lam ({v0, v1}) =
      lam f0x0 + (lam f0x1 + (lam f0xx + (lam fx00 + (lam fx01 + (lam fx0x + (lam fxx0 + (lam fxx1 + (lam fxxx)))))))) := by
  unfold cutValue
  calc
    _ = (([f0x0, f0x1, f0xx, fx00, fx01, fx0x, fxx0, fxx1, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem pair02 (lam : Face → Nat) :
    cutValue lam ({v0, v2}) =
      lam f00x + (lam f01x + (lam f0xx + (lam fx00 + (lam fx0x + (lam fx10 + (lam fx1x + (lam fxx0 + (lam fxxx)))))))) := by
  unfold cutValue
  calc
    _ = (([f00x, f01x, f0xx, fx00, fx0x, fx10, fx1x, fxx0, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem pair04 (lam : Face → Nat) :
    cutValue lam ({v0, v4}) =
      lam f00x + (lam f0x0 + (lam f0xx + (lam f10x + (lam f1x0 + (lam f1xx + (lam fx0x + (lam fxx0 + (lam fxxx)))))))) := by
  unfold cutValue
  calc
    _ = (([f00x, f0x0, f0xx, f10x, f1x0, f1xx, fx0x, fxx0, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem pair13 (lam : Face → Nat) :
    cutValue lam ({v1, v3}) =
      lam f00x + (lam f01x + (lam f0xx + (lam fx01 + (lam fx0x + (lam fx11 + (lam fx1x + (lam fxx1 + (lam fxxx)))))))) := by
  unfold cutValue
  calc
    _ = (([f00x, f01x, f0xx, fx01, fx0x, fx11, fx1x, fxx1, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem pair15 (lam : Face → Nat) :
    cutValue lam ({v1, v5}) =
      lam f00x + (lam f0x1 + (lam f0xx + (lam f10x + (lam f1x1 + (lam f1xx + (lam fx0x + (lam fxx1 + (lam fxxx)))))))) := by
  unfold cutValue
  calc
    _ = (([f00x, f0x1, f0xx, f10x, f1x1, f1xx, fx0x, fxx1, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem pair23 (lam : Face → Nat) :
    cutValue lam ({v2, v3}) =
      lam f0x0 + (lam f0x1 + (lam f0xx + (lam fx10 + (lam fx11 + (lam fx1x + (lam fxx0 + (lam fxx1 + (lam fxxx)))))))) := by
  unfold cutValue
  calc
    _ = (([f0x0, f0x1, f0xx, fx10, fx11, fx1x, fxx0, fxx1, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem pair26 (lam : Face → Nat) :
    cutValue lam ({v2, v6}) =
      lam f01x + (lam f0x0 + (lam f0xx + (lam f11x + (lam f1x0 + (lam f1xx + (lam fx1x + (lam fxx0 + (lam fxxx)))))))) := by
  unfold cutValue
  calc
    _ = (([f01x, f0x0, f0xx, f11x, f1x0, f1xx, fx1x, fxx0, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem pair37 (lam : Face → Nat) :
    cutValue lam ({v3, v7}) =
      lam f01x + (lam f0x1 + (lam f0xx + (lam f11x + (lam f1x1 + (lam f1xx + (lam fx1x + (lam fxx1 + (lam fxxx)))))))) := by
  unfold cutValue
  calc
    _ = (([f01x, f0x1, f0xx, f11x, f1x1, f1xx, fx1x, fxx1, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem pair45 (lam : Face → Nat) :
    cutValue lam ({v4, v5}) =
      lam f1x0 + (lam f1x1 + (lam f1xx + (lam fx00 + (lam fx01 + (lam fx0x + (lam fxx0 + (lam fxx1 + (lam fxxx)))))))) := by
  unfold cutValue
  calc
    _ = (([f1x0, f1x1, f1xx, fx00, fx01, fx0x, fxx0, fxx1, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem pair46 (lam : Face → Nat) :
    cutValue lam ({v4, v6}) =
      lam f10x + (lam f11x + (lam f1xx + (lam fx00 + (lam fx0x + (lam fx10 + (lam fx1x + (lam fxx0 + (lam fxxx)))))))) := by
  unfold cutValue
  calc
    _ = (([f10x, f11x, f1xx, fx00, fx0x, fx10, fx1x, fxx0, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem pair57 (lam : Face → Nat) :
    cutValue lam ({v5, v7}) =
      lam f10x + (lam f11x + (lam f1xx + (lam fx01 + (lam fx0x + (lam fx11 + (lam fx1x + (lam fxx1 + (lam fxxx)))))))) := by
  unfold cutValue
  calc
    _ = (([f10x, f11x, f1xx, fx01, fx0x, fx11, fx1x, fxx1, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem pair67 (lam : Face → Nat) :
    cutValue lam ({v6, v7}) =
      lam f1x0 + (lam f1x1 + (lam f1xx + (lam fx10 + (lam fx11 + (lam fx1x + (lam fxx0 + (lam fxx1 + (lam fxxx)))))))) := by
  unfold cutValue
  calc
    _ = (([f1x0, f1x1, f1xx, fx10, fx11, fx1x, fxx0, fxx1, fxxx] : List Face).map lam).sum :=
      CubeCertificate.sumFromList lam _ (by decide) (by decide)
    _ = _ := by simp
private theorem parityCounts (x s t k : Nat)
    (h : 3*x + 2*s + t = 3*k) (g : 4*k ≤ 4*x + 2*s + t) :
    x = k ∧ s + t = 0 := by omega
private theorem cycleCounts (x s t u k : Nat)
    (h : 3*x + 2*s + t + u = 3*k) (g : 6*k ≤ 6*x + 3*s + 2*t + u) :
    s + u = 0 ∧ 6*x + 2*t = 6*k := by omega
private theorem tightSix (k a b c d e f : Nat)
    (ha : k ≤ a) (hb : k ≤ b) (hc : k ≤ c) (hd : k ≤ d) (he : k ≤ e) (hf : k ≤ f)
    (hs : a + b + c + d + e + f = 6*k) :
    a = k ∧ b = k ∧ c = k ∧ d = k ∧ e = k ∧ f = k := by omega
private theorem equalWeights (x k a b c d e f : Nat)
    (v0 : x + f + a = k) (v1 : x + a + b = k) (v2 : x + b + c = k)
    (v3 : x + c + d = k) (v4 : x + d + e = k) (_v5 : x + e + f = k)
    (p0 : k ≤ x + f + b) (p3 : k ≤ x + c + e) :
    b = a ∧ c = a ∧ d = a ∧ e = a ∧ f = a ∧ 2*a ≤ k ∧ x = k - 2*a := by omega
private theorem case0 (S : Finset (Finset Vertex))  (lam : Face → Nat) (k : Nat) (R : Finset Vertex)
    (hc : ∀ i : Fin 3, cutValue lam (univ.filter fun v => v i = false) = k)
    (single : ∀ u ∈ R, k ≤ cutValue lam {u})
    (hh : ∀ A : Finset Vertex, A ∈ S → (∃ r ∈ R, r ∈ A) →
      (∃ r ∈ R, r ∉ A) → k ≤ cutValue lam A)
    (r0 : v0 ∈ R) (r3 : v3 ∈ R) (r5 : v5 ∈ R) (r6 : v6 ∈ R) : IsFlower lam k := by
  have c0 := hc 0
  rw [coord0] at c0
  have c1 := hc 1
  rw [coord1] at c1
  have c2 := hc 2
  rw [coord2] at c2
  have hatomic0 := single v0 r0
  rw [atomic0] at hatomic0
  have hatomic3 := single v3 r3
  rw [atomic3] at hatomic3
  have hatomic5 := single v5 r5
  rw [atomic5] at hatomic5
  have hatomic6 := single v6 r6
  rw [atomic6] at hatomic6
  have coords := congrArg₂ (· + ·) (congrArg₂ (· + ·) c0 c1) c2
  have atoms := (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hatomic0 hatomic3) hatomic5) hatomic6)
  obtain ⟨full, zeroTotal⟩ := parityCounts (lam fxxx) (lam f0xx + lam f1xx + lam fx0x + lam fx1x + lam fxx0 + lam fxx1) (lam f00x + lam f01x + lam f0x0 + lam f0x1 + lam f10x + lam f11x + lam f1x0 + lam f1x1 + lam fx00 + lam fx01 + lam fx10 + lam fx11) k (by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 atoms; omega) (by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords; omega)
  have zf00x : lam f00x = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full; omega
  have zf01x : lam f01x = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x; omega
  have zf0x0 : lam f0x0 = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x zf01x; omega
  have zf0x1 : lam f0x1 = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x zf01x zf0x0; omega
  have zf10x : lam f10x = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x zf01x zf0x0 zf0x1; omega
  have zf11x : lam f11x = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x; omega
  have zf1x0 : lam f1x0 = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x; omega
  have zf1x1 : lam f1x1 = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0; omega
  have zfx00 : lam fx00 = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1; omega
  have zfx01 : lam fx01 = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00; omega
  have zfx10 : lam fx10 = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00 zfx01; omega
  have zfx11 : lam fx11 = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00 zfx01 zfx10; omega
  have zf0xx : lam f0xx = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00 zfx01 zfx10 zfx11; omega
  have zf1xx : lam f1xx = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00 zfx01 zfx10 zfx11 zf0xx; omega
  have zfx0x : lam fx0x = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00 zfx01 zfx10 zfx11 zf0xx zf1xx; omega
  have zfx1x : lam fx1x = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00 zfx01 zfx10 zfx11 zf0xx zf1xx zfx0x; omega
  have zfxx0 : lam fxx0 = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00 zfx01 zfx10 zfx11 zf0xx zf1xx zfx0x zfx1x; omega
  have zfxx1 : lam fxx1 = 0 := by clear c0 c1 c2 hatomic0 hatomic3 hatomic5 hatomic6 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00 zfx01 zfx10 zfx11 zf0xx zf1xx zfx0x zfx1x zfxx0; omega
  refine ⟨?_, v0, 0, ?_, ?_, ?_⟩
  · intro f h
    rcases dimension2 f h with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact Nat.zero_le _
  · change lam fxxx = _
    simpa using full
  · intro f h
    rcases dimension1 f h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
    all_goals assumption
private theorem case1 (S : Finset (Finset Vertex))  (lam : Face → Nat) (k : Nat) (R : Finset Vertex)
    (hc : ∀ i : Fin 3, cutValue lam (univ.filter fun v => v i = false) = k)
    (single : ∀ u ∈ R, k ≤ cutValue lam {u})
    (hh : ∀ A : Finset Vertex, A ∈ S → (∃ r ∈ R, r ∈ A) →
      (∃ r ∈ R, r ∉ A) → k ≤ cutValue lam A)
    (r1 : v1 ∈ R) (r2 : v2 ∈ R) (r4 : v4 ∈ R) (r7 : v7 ∈ R) : IsFlower lam k := by
  have c0 := hc 0
  rw [coord0] at c0
  have c1 := hc 1
  rw [coord1] at c1
  have c2 := hc 2
  rw [coord2] at c2
  have hatomic1 := single v1 r1
  rw [atomic1] at hatomic1
  have hatomic2 := single v2 r2
  rw [atomic2] at hatomic2
  have hatomic4 := single v4 r4
  rw [atomic4] at hatomic4
  have hatomic7 := single v7 r7
  rw [atomic7] at hatomic7
  have coords := congrArg₂ (· + ·) (congrArg₂ (· + ·) c0 c1) c2
  have atoms := (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hatomic1 hatomic2) hatomic4) hatomic7)
  obtain ⟨full, zeroTotal⟩ := parityCounts (lam fxxx) (lam f0xx + lam f1xx + lam fx0x + lam fx1x + lam fxx0 + lam fxx1) (lam f00x + lam f01x + lam f0x0 + lam f0x1 + lam f10x + lam f11x + lam f1x0 + lam f1x1 + lam fx00 + lam fx01 + lam fx10 + lam fx11) k (by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 atoms; omega) (by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords; omega)
  have zf00x : lam f00x = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full; omega
  have zf01x : lam f01x = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x; omega
  have zf0x0 : lam f0x0 = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x zf01x; omega
  have zf0x1 : lam f0x1 = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x zf01x zf0x0; omega
  have zf10x : lam f10x = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x zf01x zf0x0 zf0x1; omega
  have zf11x : lam f11x = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x; omega
  have zf1x0 : lam f1x0 = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x; omega
  have zf1x1 : lam f1x1 = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0; omega
  have zfx00 : lam fx00 = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1; omega
  have zfx01 : lam fx01 = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00; omega
  have zfx10 : lam fx10 = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00 zfx01; omega
  have zfx11 : lam fx11 = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00 zfx01 zfx10; omega
  have zf0xx : lam f0xx = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00 zfx01 zfx10 zfx11; omega
  have zf1xx : lam f1xx = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00 zfx01 zfx10 zfx11 zf0xx; omega
  have zfx0x : lam fx0x = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00 zfx01 zfx10 zfx11 zf0xx zf1xx; omega
  have zfx1x : lam fx1x = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00 zfx01 zfx10 zfx11 zf0xx zf1xx zfx0x; omega
  have zfxx0 : lam fxx0 = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00 zfx01 zfx10 zfx11 zf0xx zf1xx zfx0x zfx1x; omega
  have zfxx1 : lam fxx1 = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic4 hatomic7 coords atoms full zf00x zf01x zf0x0 zf0x1 zf10x zf11x zf1x0 zf1x1 zfx00 zfx01 zfx10 zfx11 zf0xx zf1xx zfx0x zfx1x zfxx0; omega
  refine ⟨?_, v0, 0, ?_, ?_, ?_⟩
  · intro f h
    rcases dimension2 f h with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact Nat.zero_le _
  · change lam fxxx = _
    simpa using full
  · intro f h
    rcases dimension1 f h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
    all_goals assumption
private theorem case2 (S : Finset (Finset Vertex)) (hits0 : ∃ A ∈ AlternatingMatching 0, A ∈ S) (hits1 : ∃ A ∈ AlternatingMatching 1, A ∈ S) (lam : Face → Nat) (k : Nat) (R : Finset Vertex)
    (hc : ∀ i : Fin 3, cutValue lam (univ.filter fun v => v i = false) = k)
    (single : ∀ u ∈ R, k ≤ cutValue lam {u})
    (hh : ∀ A : Finset Vertex, A ∈ S → (∃ r ∈ R, r ∈ A) →
      (∃ r ∈ R, r ∉ A) → k ≤ cutValue lam A)
    (r1 : v1 ∈ R) (r2 : v2 ∈ R) (r3 : v3 ∈ R) (r4 : v4 ∈ R) (r5 : v5 ∈ R) (r6 : v6 ∈ R) : IsFlower lam k := by
  have c0 := hc 0
  rw [coord0] at c0
  have c1 := hc 1
  rw [coord1] at c1
  have c2 := hc 2
  rw [coord2] at c2
  have hatomic1 := single v1 r1
  rw [atomic1] at hatomic1
  have hatomic2 := single v2 r2
  rw [atomic2] at hatomic2
  have hatomic3 := single v3 r3
  rw [atomic3] at hatomic3
  have hatomic4 := single v4 r4
  rw [atomic4] at hatomic4
  have hatomic5 := single v5 r5
  rw [atomic5] at hatomic5
  have hatomic6 := single v6 r6
  rw [atomic6] at hatomic6
  have hpair13 (chosen : {v1, v3} ∈ S) := hh {v1, v3} chosen ⟨v1, r1, by decide⟩ ⟨v2, r2, by decide⟩
  rw [pair13] at hpair13
  have hpair15 (chosen : {v1, v5} ∈ S) := hh {v1, v5} chosen ⟨v1, r1, by decide⟩ ⟨v2, r2, by decide⟩
  rw [pair15] at hpair15
  have hpair23 (chosen : {v2, v3} ∈ S) := hh {v2, v3} chosen ⟨v2, r2, by decide⟩ ⟨v1, r1, by decide⟩
  rw [pair23] at hpair23
  have hpair26 (chosen : {v2, v6} ∈ S) := hh {v2, v6} chosen ⟨v2, r2, by decide⟩ ⟨v1, r1, by decide⟩
  rw [pair26] at hpair26
  have hpair45 (chosen : {v4, v5} ∈ S) := hh {v4, v5} chosen ⟨v4, r4, by decide⟩ ⟨v1, r1, by decide⟩
  rw [pair45] at hpair45
  have hpair46 (chosen : {v4, v6} ∈ S) := hh {v4, v6} chosen ⟨v4, r4, by decide⟩ ⟨v1, r1, by decide⟩
  rw [pair46] at hpair46
  have coords := congrArg₂ (· + ·) (congrArg₂ (· + ·) c0 c1) c2
  have atoms := (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hatomic1 hatomic2) hatomic3) hatomic4) hatomic5) hatomic6)
  obtain ⟨zeroTotal, balance⟩ := cycleCounts (lam fxxx) (lam f0xx + lam f1xx + lam fx0x + lam fx1x + lam fxx0 + lam fxx1) (lam f01x + lam f0x1 + lam f10x + lam f1x0 + lam fx01 + lam fx10) (lam f00x + lam f0x0 + lam f11x + lam f1x1 + lam fx00 + lam fx11) k (by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 atoms; omega) (by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords; omega)
  have zf0xx : lam f0xx = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms balance; omega
  have zf1xx : lam f1xx = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms balance zf0xx; omega
  have zfx0x : lam fx0x = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms balance zf0xx zf1xx; omega
  have zfx1x : lam fx1x = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms balance zf0xx zf1xx zfx0x; omega
  have zfxx0 : lam fxx0 = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms balance zf0xx zf1xx zfx0x zfx1x; omega
  have zfxx1 : lam fxx1 = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0; omega
  have zf00x : lam f00x = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1; omega
  have zf0x0 : lam f0x0 = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x; omega
  have zf11x : lam f11x = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0; omega
  have zf1x1 : lam f1x1 = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0 zf11x; omega
  have zfx00 : lam fx00 = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0 zf11x zf1x1; omega
  have zfx11 : lam fx11 = 0 := by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0 zf11x zf1x1 zfx00; omega
  simp only [zf00x, zf0xx, zfx0x, zfxx1, Nat.zero_add] at hatomic1
  simp only [zf0x0, zf0xx, zfx1x, zfxx0, Nat.zero_add] at hatomic2
  simp only [zf0xx, zfx11, zfx1x, zfxx1, Nat.zero_add] at hatomic3
  simp only [zf1xx, zfx00, zfx0x, zfxx0, Nat.zero_add] at hatomic4
  simp only [zf1x1, zf1xx, zfx0x, zfxx1, Nat.zero_add] at hatomic5
  simp only [zf11x, zf1xx, zfx1x, zfxx0, Nat.zero_add] at hatomic6
  simp only [zf00x, zf0xx, zfx0x, zfx11, zfx1x, zfxx1, Nat.zero_add] at hpair13
  simp only [zf00x, zf0xx, zf1x1, zf1xx, zfx0x, zfxx1, Nat.zero_add] at hpair15
  simp only [zf0x0, zf0xx, zfx11, zfx1x, zfxx0, zfxx1, Nat.zero_add] at hpair23
  simp only [zf0x0, zf0xx, zf11x, zf1xx, zfx1x, zfxx0, Nat.zero_add] at hpair26
  simp only [zf1x1, zf1xx, zfx00, zfx0x, zfxx0, zfxx1, Nat.zero_add] at hpair45
  simp only [zf11x, zf1xx, zfx00, zfx0x, zfx1x, zfxx0, Nat.zero_add] at hpair46
  obtain ⟨s0,s1,s2,s3,s4,s5⟩ := tightSix k _ _ _ _ _ _ hatomic1 hatomic3 hatomic2 hatomic6 hatomic4 hatomic5 (by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms zeroTotal zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0 zf11x zf1x1 zfx00 zfx11; omega)
  have matching0 : AlternatingMatching 0 = {{v1, v3}, {v2, v6}, {v4, v5}} := by decide
  have pairBound0 : k ≤ lam fxxx + lam fx01 + lam f01x := by
    obtain ⟨A, hA, chosen⟩ := hits0
    rw [matching0] at hA
    simp only [mem_insert, mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · have test := hpair13 chosen
      clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0 zf11x zf1x1 zfx00 zfx11; omega
    · have test := hpair26 chosen
      clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0 zf11x zf1x1 zfx00 zfx11; omega
    · have test := hpair45 chosen
      clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0 zf11x zf1x1 zfx00 zfx11; omega
  have matching1 : AlternatingMatching 1 = {{v1, v5}, {v2, v3}, {v4, v6}} := by decide
  have pairBound1 : k ≤ lam fxxx + lam fx10 + lam f10x := by
    obtain ⟨A, hA, chosen⟩ := hits1
    rw [matching1] at hA
    simp only [mem_insert, mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · have test := hpair15 chosen
      clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0 zf11x zf1x1 zfx00 zfx11; omega
    · have test := hpair23 chosen
      clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0 zf11x zf1x1 zfx00 zfx11; omega
    · have test := hpair46 chosen
      clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0 zf11x zf1x1 zfx00 zfx11; omega
  obtain ⟨eq1,eq2,eq3,eq4,eq5,bound,full⟩ := equalWeights (lam fxxx) k (lam f0x1) (lam f01x) (lam fx10) (lam f1x0) (lam f10x) (lam fx01)
    (by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0 zf11x zf1x1 zfx00 zfx11 s1 s2 s3 s4 s5; omega)
    (by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0 zf11x zf1x1 zfx00 zfx11 s0 s2 s3 s4 s5; omega)
    (by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0 zf11x zf1x1 zfx00 zfx11 s0 s1 s3 s4 s5; omega)
    (by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0 zf11x zf1x1 zfx00 zfx11 s0 s1 s2 s4 s5; omega)
    (by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0 zf11x zf1x1 zfx00 zfx11 s0 s1 s2 s3 s5; omega)
    (by clear c0 c1 c2 hatomic1 hatomic2 hatomic3 hatomic4 hatomic5 hatomic6 hpair13 hpair15 hpair23 hpair26 hpair45 hpair46 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x0 zf11x zf1x1 zfx00 zfx11 s0 s1 s2 s3 s4; omega)
    pairBound0
    pairBound1
  refine ⟨?_, v0, lam f0x1, ?_, ?_, ?_⟩
  · intro f h
    rcases dimension2 f h with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact bound
  · exact full
  · intro f h
    rcases dimension1 f h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
    all_goals assumption
private theorem case3 (S : Finset (Finset Vertex)) (hits2 : ∃ A ∈ AlternatingMatching 2, A ∈ S) (hits3 : ∃ A ∈ AlternatingMatching 3, A ∈ S) (lam : Face → Nat) (k : Nat) (R : Finset Vertex)
    (hc : ∀ i : Fin 3, cutValue lam (univ.filter fun v => v i = false) = k)
    (single : ∀ u ∈ R, k ≤ cutValue lam {u})
    (hh : ∀ A : Finset Vertex, A ∈ S → (∃ r ∈ R, r ∈ A) →
      (∃ r ∈ R, r ∉ A) → k ≤ cutValue lam A)
    (r0 : v0 ∈ R) (r2 : v2 ∈ R) (r3 : v3 ∈ R) (r4 : v4 ∈ R) (r5 : v5 ∈ R) (r7 : v7 ∈ R) : IsFlower lam k := by
  have c0 := hc 0
  rw [coord0] at c0
  have c1 := hc 1
  rw [coord1] at c1
  have c2 := hc 2
  rw [coord2] at c2
  have hatomic0 := single v0 r0
  rw [atomic0] at hatomic0
  have hatomic2 := single v2 r2
  rw [atomic2] at hatomic2
  have hatomic3 := single v3 r3
  rw [atomic3] at hatomic3
  have hatomic4 := single v4 r4
  rw [atomic4] at hatomic4
  have hatomic5 := single v5 r5
  rw [atomic5] at hatomic5
  have hatomic7 := single v7 r7
  rw [atomic7] at hatomic7
  have hpair02 (chosen : {v0, v2} ∈ S) := hh {v0, v2} chosen ⟨v0, r0, by decide⟩ ⟨v3, r3, by decide⟩
  rw [pair02] at hpair02
  have hpair04 (chosen : {v0, v4} ∈ S) := hh {v0, v4} chosen ⟨v0, r0, by decide⟩ ⟨v2, r2, by decide⟩
  rw [pair04] at hpair04
  have hpair23 (chosen : {v2, v3} ∈ S) := hh {v2, v3} chosen ⟨v2, r2, by decide⟩ ⟨v0, r0, by decide⟩
  rw [pair23] at hpair23
  have hpair37 (chosen : {v3, v7} ∈ S) := hh {v3, v7} chosen ⟨v3, r3, by decide⟩ ⟨v0, r0, by decide⟩
  rw [pair37] at hpair37
  have hpair45 (chosen : {v4, v5} ∈ S) := hh {v4, v5} chosen ⟨v4, r4, by decide⟩ ⟨v0, r0, by decide⟩
  rw [pair45] at hpair45
  have hpair57 (chosen : {v5, v7} ∈ S) := hh {v5, v7} chosen ⟨v5, r5, by decide⟩ ⟨v0, r0, by decide⟩
  rw [pair57] at hpair57
  have coords := congrArg₂ (· + ·) (congrArg₂ (· + ·) c0 c1) c2
  have atoms := (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hatomic0 hatomic2) hatomic3) hatomic4) hatomic5) hatomic7)
  obtain ⟨zeroTotal, balance⟩ := cycleCounts (lam fxxx) (lam f0xx + lam f1xx + lam fx0x + lam fx1x + lam fxx0 + lam fxx1) (lam f01x + lam f0x0 + lam f10x + lam f1x1 + lam fx00 + lam fx11) (lam f00x + lam f0x1 + lam f11x + lam f1x0 + lam fx01 + lam fx10) k (by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 atoms; omega) (by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords; omega)
  have zf0xx : lam f0xx = 0 := by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms balance; omega
  have zf1xx : lam f1xx = 0 := by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms balance zf0xx; omega
  have zfx0x : lam fx0x = 0 := by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms balance zf0xx zf1xx; omega
  have zfx1x : lam fx1x = 0 := by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms balance zf0xx zf1xx zfx0x; omega
  have zfxx0 : lam fxx0 = 0 := by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms balance zf0xx zf1xx zfx0x zfx1x; omega
  have zfxx1 : lam fxx1 = 0 := by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0; omega
  have zf00x : lam f00x = 0 := by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1; omega
  have zf0x1 : lam f0x1 = 0 := by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x; omega
  have zf11x : lam f11x = 0 := by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1; omega
  have zf1x0 : lam f1x0 = 0 := by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1 zf11x; omega
  have zfx01 : lam fx01 = 0 := by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1 zf11x zf1x0; omega
  have zfx10 : lam fx10 = 0 := by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1 zf11x zf1x0 zfx01; omega
  simp only [zf00x, zf0xx, zfx0x, zfxx0, Nat.zero_add] at hatomic0
  simp only [zf0xx, zfx10, zfx1x, zfxx0, Nat.zero_add] at hatomic2
  simp only [zf0x1, zf0xx, zfx1x, zfxx1, Nat.zero_add] at hatomic3
  simp only [zf1x0, zf1xx, zfx0x, zfxx0, Nat.zero_add] at hatomic4
  simp only [zf1xx, zfx01, zfx0x, zfxx1, Nat.zero_add] at hatomic5
  simp only [zf11x, zf1xx, zfx1x, zfxx1, Nat.zero_add] at hatomic7
  simp only [zf00x, zf0xx, zfx0x, zfx10, zfx1x, zfxx0, Nat.zero_add] at hpair02
  simp only [zf00x, zf0xx, zf1x0, zf1xx, zfx0x, zfxx0, Nat.zero_add] at hpair04
  simp only [zf0x1, zf0xx, zfx10, zfx1x, zfxx0, zfxx1, Nat.zero_add] at hpair23
  simp only [zf0x1, zf0xx, zf11x, zf1xx, zfx1x, zfxx1, Nat.zero_add] at hpair37
  simp only [zf1x0, zf1xx, zfx01, zfx0x, zfxx0, zfxx1, Nat.zero_add] at hpair45
  simp only [zf11x, zf1xx, zfx01, zfx0x, zfx1x, zfxx1, Nat.zero_add] at hpair57
  obtain ⟨s0,s1,s2,s3,s4,s5⟩ := tightSix k _ _ _ _ _ _ hatomic0 hatomic2 hatomic3 hatomic7 hatomic5 hatomic4 (by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms zeroTotal zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1 zf11x zf1x0 zfx01 zfx10; omega)
  have matching0 : AlternatingMatching 2 = {{v0, v2}, {v3, v7}, {v4, v5}} := by decide
  have pairBound0 : k ≤ lam fxxx + lam fx00 + lam f01x := by
    obtain ⟨A, hA, chosen⟩ := hits2
    rw [matching0] at hA
    simp only [mem_insert, mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · have test := hpair02 chosen
      clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1 zf11x zf1x0 zfx01 zfx10; omega
    · have test := hpair37 chosen
      clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1 zf11x zf1x0 zfx01 zfx10; omega
    · have test := hpair45 chosen
      clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1 zf11x zf1x0 zfx01 zfx10; omega
  have matching1 : AlternatingMatching 3 = {{v0, v4}, {v2, v3}, {v5, v7}} := by decide
  have pairBound1 : k ≤ lam fxxx + lam fx11 + lam f10x := by
    obtain ⟨A, hA, chosen⟩ := hits3
    rw [matching1] at hA
    simp only [mem_insert, mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · have test := hpair04 chosen
      clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1 zf11x zf1x0 zfx01 zfx10; omega
    · have test := hpair23 chosen
      clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1 zf11x zf1x0 zfx01 zfx10; omega
    · have test := hpair57 chosen
      clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1 zf11x zf1x0 zfx01 zfx10; omega
  obtain ⟨eq1,eq2,eq3,eq4,eq5,bound,full⟩ := equalWeights (lam fxxx) k (lam f0x0) (lam f01x) (lam fx11) (lam f1x1) (lam f10x) (lam fx00)
    (by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1 zf11x zf1x0 zfx01 zfx10 s1 s2 s3 s4 s5; omega)
    (by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1 zf11x zf1x0 zfx01 zfx10 s0 s2 s3 s4 s5; omega)
    (by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1 zf11x zf1x0 zfx01 zfx10 s0 s1 s3 s4 s5; omega)
    (by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1 zf11x zf1x0 zfx01 zfx10 s0 s1 s2 s4 s5; omega)
    (by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1 zf11x zf1x0 zfx01 zfx10 s0 s1 s2 s3 s5; omega)
    (by clear c0 c1 c2 hatomic0 hatomic2 hatomic3 hatomic4 hatomic5 hatomic7 hpair02 hpair04 hpair23 hpair37 hpair45 hpair57 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf00x zf0x1 zf11x zf1x0 zfx01 zfx10 s0 s1 s2 s3 s4; omega)
    pairBound0
    pairBound1
  refine ⟨?_, v1, lam f0x0, ?_, ?_, ?_⟩
  · intro f h
    rcases dimension2 f h with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact bound
  · exact full
  · intro f h
    rcases dimension1 f h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
    all_goals assumption
private theorem case4 (S : Finset (Finset Vertex)) (hits4 : ∃ A ∈ AlternatingMatching 4, A ∈ S) (hits5 : ∃ A ∈ AlternatingMatching 5, A ∈ S) (lam : Face → Nat) (k : Nat) (R : Finset Vertex)
    (hc : ∀ i : Fin 3, cutValue lam (univ.filter fun v => v i = false) = k)
    (single : ∀ u ∈ R, k ≤ cutValue lam {u})
    (hh : ∀ A : Finset Vertex, A ∈ S → (∃ r ∈ R, r ∈ A) →
      (∃ r ∈ R, r ∉ A) → k ≤ cutValue lam A)
    (r0 : v0 ∈ R) (r1 : v1 ∈ R) (r3 : v3 ∈ R) (r4 : v4 ∈ R) (r6 : v6 ∈ R) (r7 : v7 ∈ R) : IsFlower lam k := by
  have c0 := hc 0
  rw [coord0] at c0
  have c1 := hc 1
  rw [coord1] at c1
  have c2 := hc 2
  rw [coord2] at c2
  have hatomic0 := single v0 r0
  rw [atomic0] at hatomic0
  have hatomic1 := single v1 r1
  rw [atomic1] at hatomic1
  have hatomic3 := single v3 r3
  rw [atomic3] at hatomic3
  have hatomic4 := single v4 r4
  rw [atomic4] at hatomic4
  have hatomic6 := single v6 r6
  rw [atomic6] at hatomic6
  have hatomic7 := single v7 r7
  rw [atomic7] at hatomic7
  have hpair01 (chosen : {v0, v1} ∈ S) := hh {v0, v1} chosen ⟨v0, r0, by decide⟩ ⟨v3, r3, by decide⟩
  rw [pair01] at hpair01
  have hpair04 (chosen : {v0, v4} ∈ S) := hh {v0, v4} chosen ⟨v0, r0, by decide⟩ ⟨v1, r1, by decide⟩
  rw [pair04] at hpair04
  have hpair13 (chosen : {v1, v3} ∈ S) := hh {v1, v3} chosen ⟨v1, r1, by decide⟩ ⟨v0, r0, by decide⟩
  rw [pair13] at hpair13
  have hpair37 (chosen : {v3, v7} ∈ S) := hh {v3, v7} chosen ⟨v3, r3, by decide⟩ ⟨v0, r0, by decide⟩
  rw [pair37] at hpair37
  have hpair46 (chosen : {v4, v6} ∈ S) := hh {v4, v6} chosen ⟨v4, r4, by decide⟩ ⟨v0, r0, by decide⟩
  rw [pair46] at hpair46
  have hpair67 (chosen : {v6, v7} ∈ S) := hh {v6, v7} chosen ⟨v6, r6, by decide⟩ ⟨v0, r0, by decide⟩
  rw [pair67] at hpair67
  have coords := congrArg₂ (· + ·) (congrArg₂ (· + ·) c0 c1) c2
  have atoms := (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hatomic0 hatomic1) hatomic3) hatomic4) hatomic6) hatomic7)
  obtain ⟨zeroTotal, balance⟩ := cycleCounts (lam fxxx) (lam f0xx + lam f1xx + lam fx0x + lam fx1x + lam fxx0 + lam fxx1) (lam f00x + lam f0x1 + lam f11x + lam f1x0 + lam fx00 + lam fx11) (lam f01x + lam f0x0 + lam f10x + lam f1x1 + lam fx01 + lam fx10) k (by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 atoms; omega) (by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords; omega)
  have zf0xx : lam f0xx = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms balance; omega
  have zf1xx : lam f1xx = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms balance zf0xx; omega
  have zfx0x : lam fx0x = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms balance zf0xx zf1xx; omega
  have zfx1x : lam fx1x = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms balance zf0xx zf1xx zfx0x; omega
  have zfxx0 : lam fxx0 = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms balance zf0xx zf1xx zfx0x zfx1x; omega
  have zfxx1 : lam fxx1 = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0; omega
  have zf01x : lam f01x = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1; omega
  have zf0x0 : lam f0x0 = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x; omega
  have zf10x : lam f10x = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0; omega
  have zf1x1 : lam f1x1 = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0 zf10x; omega
  have zfx01 : lam fx01 = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0 zf10x zf1x1; omega
  have zfx10 : lam fx10 = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0 zf10x zf1x1 zfx01; omega
  simp only [zf0x0, zf0xx, zfx0x, zfxx0, Nat.zero_add] at hatomic0
  simp only [zf0xx, zfx01, zfx0x, zfxx1, Nat.zero_add] at hatomic1
  simp only [zf01x, zf0xx, zfx1x, zfxx1, Nat.zero_add] at hatomic3
  simp only [zf10x, zf1xx, zfx0x, zfxx0, Nat.zero_add] at hatomic4
  simp only [zf1xx, zfx10, zfx1x, zfxx0, Nat.zero_add] at hatomic6
  simp only [zf1x1, zf1xx, zfx1x, zfxx1, Nat.zero_add] at hatomic7
  simp only [zf0x0, zf0xx, zfx01, zfx0x, zfxx0, zfxx1, Nat.zero_add] at hpair01
  simp only [zf0x0, zf0xx, zf10x, zf1xx, zfx0x, zfxx0, Nat.zero_add] at hpair04
  simp only [zf01x, zf0xx, zfx01, zfx0x, zfx1x, zfxx1, Nat.zero_add] at hpair13
  simp only [zf01x, zf0xx, zf1x1, zf1xx, zfx1x, zfxx1, Nat.zero_add] at hpair37
  simp only [zf10x, zf1xx, zfx0x, zfx10, zfx1x, zfxx0, Nat.zero_add] at hpair46
  simp only [zf1x1, zf1xx, zfx10, zfx1x, zfxx0, zfxx1, Nat.zero_add] at hpair67
  obtain ⟨s0,s1,s2,s3,s4,s5⟩ := tightSix k _ _ _ _ _ _ hatomic0 hatomic1 hatomic3 hatomic7 hatomic6 hatomic4 (by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms zeroTotal zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0 zf10x zf1x1 zfx01 zfx10; omega)
  have matching0 : AlternatingMatching 4 = {{v0, v1}, {v3, v7}, {v4, v6}} := by decide
  have pairBound0 : k ≤ lam fxxx + lam fx00 + lam f0x1 := by
    obtain ⟨A, hA, chosen⟩ := hits4
    rw [matching0] at hA
    simp only [mem_insert, mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · have test := hpair01 chosen
      clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0 zf10x zf1x1 zfx01 zfx10; omega
    · have test := hpair37 chosen
      clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0 zf10x zf1x1 zfx01 zfx10; omega
    · have test := hpair46 chosen
      clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0 zf10x zf1x1 zfx01 zfx10; omega
  have matching1 : AlternatingMatching 5 = {{v0, v4}, {v1, v3}, {v6, v7}} := by decide
  have pairBound1 : k ≤ lam fxxx + lam fx11 + lam f1x0 := by
    obtain ⟨A, hA, chosen⟩ := hits5
    rw [matching1] at hA
    simp only [mem_insert, mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · have test := hpair04 chosen
      clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0 zf10x zf1x1 zfx01 zfx10; omega
    · have test := hpair13 chosen
      clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0 zf10x zf1x1 zfx01 zfx10; omega
    · have test := hpair67 chosen
      clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0 zf10x zf1x1 zfx01 zfx10; omega
  obtain ⟨eq1,eq2,eq3,eq4,eq5,bound,full⟩ := equalWeights (lam fxxx) k (lam f00x) (lam f0x1) (lam fx11) (lam f11x) (lam f1x0) (lam fx00)
    (by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0 zf10x zf1x1 zfx01 zfx10 s1 s2 s3 s4 s5; omega)
    (by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0 zf10x zf1x1 zfx01 zfx10 s0 s2 s3 s4 s5; omega)
    (by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0 zf10x zf1x1 zfx01 zfx10 s0 s1 s3 s4 s5; omega)
    (by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0 zf10x zf1x1 zfx01 zfx10 s0 s1 s2 s4 s5; omega)
    (by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0 zf10x zf1x1 zfx01 zfx10 s0 s1 s2 s3 s5; omega)
    (by clear c0 c1 c2 hatomic0 hatomic1 hatomic3 hatomic4 hatomic6 hatomic7 hpair01 hpair04 hpair13 hpair37 hpair46 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x0 zf10x zf1x1 zfx01 zfx10 s0 s1 s2 s3 s4; omega)
    pairBound0
    pairBound1
  refine ⟨?_, v2, lam f00x, ?_, ?_, ?_⟩
  · intro f h
    rcases dimension2 f h with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact bound
  · exact full
  · intro f h
    rcases dimension1 f h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
    all_goals assumption
private theorem case5 (S : Finset (Finset Vertex)) (hits6 : ∃ A ∈ AlternatingMatching 6, A ∈ S) (hits7 : ∃ A ∈ AlternatingMatching 7, A ∈ S) (lam : Face → Nat) (k : Nat) (R : Finset Vertex)
    (hc : ∀ i : Fin 3, cutValue lam (univ.filter fun v => v i = false) = k)
    (single : ∀ u ∈ R, k ≤ cutValue lam {u})
    (hh : ∀ A : Finset Vertex, A ∈ S → (∃ r ∈ R, r ∈ A) →
      (∃ r ∈ R, r ∉ A) → k ≤ cutValue lam A)
    (r0 : v0 ∈ R) (r1 : v1 ∈ R) (r2 : v2 ∈ R) (r5 : v5 ∈ R) (r6 : v6 ∈ R) (r7 : v7 ∈ R) : IsFlower lam k := by
  have c0 := hc 0
  rw [coord0] at c0
  have c1 := hc 1
  rw [coord1] at c1
  have c2 := hc 2
  rw [coord2] at c2
  have hatomic0 := single v0 r0
  rw [atomic0] at hatomic0
  have hatomic1 := single v1 r1
  rw [atomic1] at hatomic1
  have hatomic2 := single v2 r2
  rw [atomic2] at hatomic2
  have hatomic5 := single v5 r5
  rw [atomic5] at hatomic5
  have hatomic6 := single v6 r6
  rw [atomic6] at hatomic6
  have hatomic7 := single v7 r7
  rw [atomic7] at hatomic7
  have hpair01 (chosen : {v0, v1} ∈ S) := hh {v0, v1} chosen ⟨v0, r0, by decide⟩ ⟨v2, r2, by decide⟩
  rw [pair01] at hpair01
  have hpair02 (chosen : {v0, v2} ∈ S) := hh {v0, v2} chosen ⟨v0, r0, by decide⟩ ⟨v1, r1, by decide⟩
  rw [pair02] at hpair02
  have hpair15 (chosen : {v1, v5} ∈ S) := hh {v1, v5} chosen ⟨v1, r1, by decide⟩ ⟨v0, r0, by decide⟩
  rw [pair15] at hpair15
  have hpair26 (chosen : {v2, v6} ∈ S) := hh {v2, v6} chosen ⟨v2, r2, by decide⟩ ⟨v0, r0, by decide⟩
  rw [pair26] at hpair26
  have hpair57 (chosen : {v5, v7} ∈ S) := hh {v5, v7} chosen ⟨v5, r5, by decide⟩ ⟨v0, r0, by decide⟩
  rw [pair57] at hpair57
  have hpair67 (chosen : {v6, v7} ∈ S) := hh {v6, v7} chosen ⟨v6, r6, by decide⟩ ⟨v0, r0, by decide⟩
  rw [pair67] at hpair67
  have coords := congrArg₂ (· + ·) (congrArg₂ (· + ·) c0 c1) c2
  have atoms := (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hatomic0 hatomic1) hatomic2) hatomic5) hatomic6) hatomic7)
  obtain ⟨zeroTotal, balance⟩ := cycleCounts (lam fxxx) (lam f0xx + lam f1xx + lam fx0x + lam fx1x + lam fxx0 + lam fxx1) (lam f00x + lam f0x0 + lam f11x + lam f1x1 + lam fx01 + lam fx10) (lam f01x + lam f0x1 + lam f10x + lam f1x0 + lam fx00 + lam fx11) k (by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 atoms; omega) (by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords; omega)
  have zf0xx : lam f0xx = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms balance; omega
  have zf1xx : lam f1xx = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms balance zf0xx; omega
  have zfx0x : lam fx0x = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms balance zf0xx zf1xx; omega
  have zfx1x : lam fx1x = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms balance zf0xx zf1xx zfx0x; omega
  have zfxx0 : lam fxx0 = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms balance zf0xx zf1xx zfx0x zfx1x; omega
  have zfxx1 : lam fxx1 = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0; omega
  have zf01x : lam f01x = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1; omega
  have zf0x1 : lam f0x1 = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x; omega
  have zf10x : lam f10x = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1; omega
  have zf1x0 : lam f1x0 = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1 zf10x; omega
  have zfx00 : lam fx00 = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1 zf10x zf1x0; omega
  have zfx11 : lam fx11 = 0 := by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1 zf10x zf1x0 zfx00; omega
  simp only [zf0xx, zfx00, zfx0x, zfxx0, Nat.zero_add] at hatomic0
  simp only [zf0x1, zf0xx, zfx0x, zfxx1, Nat.zero_add] at hatomic1
  simp only [zf01x, zf0xx, zfx1x, zfxx0, Nat.zero_add] at hatomic2
  simp only [zf10x, zf1xx, zfx0x, zfxx1, Nat.zero_add] at hatomic5
  simp only [zf1x0, zf1xx, zfx1x, zfxx0, Nat.zero_add] at hatomic6
  simp only [zf1xx, zfx11, zfx1x, zfxx1, Nat.zero_add] at hatomic7
  simp only [zf0x1, zf0xx, zfx00, zfx0x, zfxx0, zfxx1, Nat.zero_add] at hpair01
  simp only [zf01x, zf0xx, zfx00, zfx0x, zfx1x, zfxx0, Nat.zero_add] at hpair02
  simp only [zf0x1, zf0xx, zf10x, zf1xx, zfx0x, zfxx1, Nat.zero_add] at hpair15
  simp only [zf01x, zf0xx, zf1x0, zf1xx, zfx1x, zfxx0, Nat.zero_add] at hpair26
  simp only [zf10x, zf1xx, zfx0x, zfx11, zfx1x, zfxx1, Nat.zero_add] at hpair57
  simp only [zf1x0, zf1xx, zfx11, zfx1x, zfxx0, zfxx1, Nat.zero_add] at hpair67
  obtain ⟨s0,s1,s2,s3,s4,s5⟩ := tightSix k _ _ _ _ _ _ hatomic0 hatomic1 hatomic5 hatomic7 hatomic6 hatomic2 (by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms zeroTotal zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1 zf10x zf1x0 zfx00 zfx11; omega)
  have matching0 : AlternatingMatching 6 = {{v0, v1}, {v2, v6}, {v5, v7}} := by decide
  have pairBound0 : k ≤ lam fxxx + lam f0x0 + lam fx01 := by
    obtain ⟨A, hA, chosen⟩ := hits6
    rw [matching0] at hA
    simp only [mem_insert, mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · have test := hpair01 chosen
      clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1 zf10x zf1x0 zfx00 zfx11; omega
    · have test := hpair26 chosen
      clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1 zf10x zf1x0 zfx00 zfx11; omega
    · have test := hpair57 chosen
      clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1 zf10x zf1x0 zfx00 zfx11; omega
  have matching1 : AlternatingMatching 7 = {{v0, v2}, {v1, v5}, {v6, v7}} := by decide
  have pairBound1 : k ≤ lam fxxx + lam f1x1 + lam fx10 := by
    obtain ⟨A, hA, chosen⟩ := hits7
    rw [matching1] at hA
    simp only [mem_insert, mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · have test := hpair02 chosen
      clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1 zf10x zf1x0 zfx00 zfx11; omega
    · have test := hpair15 chosen
      clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1 zf10x zf1x0 zfx00 zfx11; omega
    · have test := hpair67 chosen
      clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1 zf10x zf1x0 zfx00 zfx11; omega
  obtain ⟨eq1,eq2,eq3,eq4,eq5,bound,full⟩ := equalWeights (lam fxxx) k (lam f00x) (lam fx01) (lam f1x1) (lam f11x) (lam fx10) (lam f0x0)
    (by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1 zf10x zf1x0 zfx00 zfx11 s1 s2 s3 s4 s5; omega)
    (by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1 zf10x zf1x0 zfx00 zfx11 s0 s2 s3 s4 s5; omega)
    (by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1 zf10x zf1x0 zfx00 zfx11 s0 s1 s3 s4 s5; omega)
    (by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1 zf10x zf1x0 zfx00 zfx11 s0 s1 s2 s4 s5; omega)
    (by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1 zf10x zf1x0 zfx00 zfx11 s0 s1 s2 s3 s5; omega)
    (by clear c0 c1 c2 hatomic0 hatomic1 hatomic2 hatomic5 hatomic6 hatomic7 hpair01 hpair02 hpair15 hpair26 hpair57 hpair67 coords atoms zeroTotal balance zf0xx zf1xx zfx0x zfx1x zfxx0 zfxx1 zf01x zf0x1 zf10x zf1x0 zfx00 zfx11 s0 s1 s2 s3 s4; omega)
    pairBound0
    pairBound1
  refine ⟨?_, v3, lam f00x, ?_, ?_, ?_⟩
  · intro f h
    rcases dimension2 f h with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · exact bound
  · exact full
  · intro f h
    rcases dimension1 f h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
    all_goals assumption
private abbrev e0 : Face := triple (.some false) (.some false) none
private abbrev e1 : Face := triple (.some false) none (.some false)
private abbrev e2 : Face := triple none (.some false) (.some false)
private abbrev e3 : Face := triple (.some false) none (.some true)
private abbrev e4 : Face := triple none (.some false) (.some true)
private abbrev e5 : Face := triple (.some false) (.some true) none
private abbrev e6 : Face := triple none (.some true) (.some false)
private abbrev e7 : Face := triple none (.some true) (.some true)
private abbrev e8 : Face := triple (.some true) (.some false) none
private abbrev e9 : Face := triple (.some true) none (.some false)
private abbrev e10 : Face := triple (.some true) none (.some true)
private abbrev e11 : Face := triple (.some true) (.some true) none

private def makeWeight (i : Fin 8) : Face → ℕ :=
  match i.val with
  | 0 => fun f => if f = e3 ∨ f = e6 ∨ f = e8 then 1 else 0
  | 1 => fun f => if f = e4 ∨ f = e5 ∨ f = e9 then 1 else 0
  | 2 => fun f => if f = e1 ∨ f = e7 ∨ f = e8 then 1 else 0
  | 3 => fun f => if f = e2 ∨ f = e5 ∨ f = e10 then 1 else 0
  | 4 => fun f => if f = e0 ∨ f = e7 ∨ f = e9 then 1 else 0
  | 5 => fun f => if f = e2 ∨ f = e3 ∨ f = e11 then 1 else 0
  | 6 => fun f => if f = e0 ∨ f = e6 ∨ f = e10 then 1 else 0
  | _ => fun f => if f = e1 ∨ f = e4 ∨ f = e11 then 1 else 0

/-- R is held fixed before quantifying over all weights and thresholds. -/
def SufficientAt (R : Finset Vertex) (S : Finset (Finset Vertex)) : Prop :=
  ∀ (w : Face → ℕ) (k : ℕ),
    (∀ i : Fin 3, cutValue w (univ.filter fun v => v i = false) = k) →
    (∀ u ∈ R, k ≤ cutValue w {u}) →
    (∀ A ∈ S, (∃ u ∈ R, u ∈ A) → (∃ u ∈ R, u ∉ A) → k ≤ cutValue w A) →
    IsFlower w k

def parityClass : Bool → Finset Vertex
  | false => {v0,v3,v5,v6}
  | true => {v1,v2,v4,v7}

theorem mem_parityClass : ∀ (p : Bool) (v : Vertex),
    v ∈ parityClass p ↔ Bool.xor (v 0) (Bool.xor (v 1) (v 2)) = p := by decide

def ring (q : Fin 4) : Finset Vertex :=
  match q.val with
  | 0 => {v1,v2,v3,v4,v5,v6}
  | 1 => {v0,v2,v3,v4,v5,v7}
  | 2 => {v0,v1,v3,v4,v6,v7}
  | _ => {v0,v1,v2,v5,v6,v7}

theorem ring_is_antidiagonal : ∀ q : Fin 4, ∃ v : Vertex,
    ring q = univ \ {v, fun i => !(v i)} := by decide

abbrev index (q : Fin 4) (b : Bool) : Fin 8 :=
  ⟨2 * q.val + b.toNat, by cases b <;> simp <;> omega⟩

/-- A selected two-vertex side meets each matching of this particular six-cycle. -/
def HitsAt (q : Fin 4) (S : Finset (Finset Vertex)) : Prop :=
  ∀ b : Bool, ∃ A ∈ AlternatingMatching (index q b), A ∈ S

private theorem disjoint_classes : ∀ q : Fin 4,
    Disjoint (AlternatingMatching (index q false)) (AlternatingMatching (index q true)) := by decide

theorem cover_classification : ∀ R : Finset Vertex,
    (∀ u v, Adj u v → u ∈ R ∨ v ∈ R) →
      (∃ p, parityClass p ⊆ R) ∨ ∃ q, R = ring q := by decide

theorem ring_has_no_parity : ∀ q : Fin 4, ∀ p : Bool, ¬parityClass p ⊆ ring q := by decide

theorem ring_is_cover : ∀ (q : Fin 4) (u v : Vertex),
    Adj u v → u ∈ ring q ∨ v ∈ ring q := by decide

theorem parity_sufficient {R : Finset Vertex} (p : Bool) (h : parityClass p ⊆ R)
    (S : Finset (Finset Vertex)) : SufficientAt R S := by
  intro w k coords single cuts
  cases p
  · exact case0 S w k R coords single cuts
      (h (by decide : v0 ∈ parityClass false)) (h (by decide : v3 ∈ parityClass false))
      (h (by decide : v5 ∈ parityClass false)) (h (by decide : v6 ∈ parityClass false))
  · exact case1 S w k R coords single cuts
      (h (by decide : v1 ∈ parityClass true)) (h (by decide : v2 ∈ parityClass true))
      (h (by decide : v4 ∈ parityClass true)) (h (by decide : v7 ∈ parityClass true))

theorem ring_sufficient_of_hits (q : Fin 4) (S : Finset (Finset Vertex))
    (hits : HitsAt q S) : SufficientAt (ring q) S := by
  intro w k coords single cuts
  rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 by omega) with rfl | rfl | rfl | rfl

  · exact case2 S (hits false) (hits true) w k (ring 0) coords single cuts (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact case3 S (hits false) (hits true) w k (ring 1) coords single cuts (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact case4 S (hits false) (hits true) w k (ring 2) coords single cuts (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact case5 S (hits false) (hits true) w k (ring 3) coords single cuts (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem singlesWitness : ∀ (q : Fin 4) (b : Bool) (u : Vertex), u ∈ ring q →
    1 ≤ cutValue (makeWeight (index q b)) {u} := by decide

private theorem coordsWitness : ∀ (j : Fin 8) (i : Fin 3),
    cutValue (makeWeight j) (univ.filter fun v => v i = false) = 1 := by decide

private theorem pairsWitness : ∀ (j : Fin 8) (u v : Vertex), Adj u v →
    {u,v} ∉ AlternatingMatching j → 1 ≤ cutValue (makeWeight j) {u,v} := by decide

private theorem witnessNotFlower (j : Fin 8) : ¬ IsFlower (makeWeight j) 1 := by
  have cube : ∀ i : Fin 8, makeWeight i (fun _ => none) = 0 := by decide
  rintro ⟨_, _, l, small, full, _⟩
  rw [cube] at full
  omega

theorem counterexample_same_ring (q : Fin 4) (S : Finset (Finset Vertex))
    (pairs : ∀ A ∈ S, AdjacentSide A) (miss : ¬ HitsAt q S) :
    ∃ w : Face → ℕ,
      (∀ i : Fin 3, cutValue w (univ.filter fun v => v i = false) = 1) ∧
      (∀ v ∈ ring q, 1 ≤ cutValue w {v}) ∧
      (∀ A ∈ S, 1 ≤ cutValue w A) ∧ ¬IsFlower w 1 := by
  classical
  obtain ⟨b, hb⟩ := not_forall.mp miss
  refine ⟨makeWeight (index q b), coordsWitness _, singlesWitness q b, ?_, witnessNotFlower _⟩
  intro A ha
  obtain ⟨u,v,adj,rfl⟩ := pairs A ha
  exact pairsWitness _ u v adj (fun hm => hb ⟨_, hm, ha⟩)

theorem ring_sufficient_iff (q : Fin 4) (S : Finset (Finset Vertex))
    (pairs : ∀ A ∈ S, AdjacentSide A) : SufficientAt (ring q) S ↔ HitsAt q S := by
  refine ⟨?_, ring_sufficient_of_hits q S⟩
  intro sufficient
  by_contra missed
  obtain ⟨w,coord,single,tests,bad⟩ := counterexample_same_ring q S pairs missed
  exact bad (sufficient w 1 coord single (fun A hA _ _ => tests A hA))

private theorem two_choices : ∀ q : Fin 4,
    ∃ u v : Vertex, ∃ a b : Vertex, Adj u v ∧ Adj a b ∧
      {u,v} ∈ AlternatingMatching (index q false) ∧ {a,b} ∈ AlternatingMatching (index q true) := by
  decide

theorem ring_minimum_two (q : Fin 4) :
    (∃ S : Finset (Finset Vertex), S.card = 2 ∧ (∀ A ∈ S, AdjacentSide A) ∧ SufficientAt (ring q) S) ∧
    (∀ S : Finset (Finset Vertex), (∀ A ∈ S, AdjacentSide A) → SufficientAt (ring q) S → 2 ≤ S.card) := by
  have separate := Finset.disjoint_left.mp (disjoint_classes q)
  constructor
  · obtain ⟨u,v,a,b,uv,ab,hm,hn⟩ := two_choices q
    let U : Finset Vertex := {u,v}
    let V : Finset Vertex := {a,b}
    have hne : U ≠ V := by
      intro h
      apply separate hm
      change U ∈ AlternatingMatching (index q true)
      rw [h]
      exact hn
    refine ⟨{U,V}, by simp [hne], ?_, ring_sufficient_of_hits _ _ ?_⟩
    · intro A ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact ⟨u,v,uv,rfl⟩
      · exact Finset.mem_singleton.mp ha ▸ (show AdjacentSide V from ⟨a,b,ab,rfl⟩)
    · intro flag
      cases flag
      · exact ⟨U, hm, by simp⟩
      · exact ⟨V, hn, by simp⟩
  · intro S pairs suff
    have h := (ring_sufficient_iff q S pairs).mp suff
    obtain ⟨a,hm,ha⟩ := h false
    obtain ⟨b,hn,hb⟩ := h true
    exact Finset.one_lt_card.mpr ⟨a,ha,b,hb,fun eq => separate hm (eq ▸ hn)⟩

/-- With at most one preselected pair, the same six-point cover admits a
counterexample even if every selected pair is checked unconditionally. -/
theorem one_test_counterexample (q : Fin 4) (S : Finset (Finset Vertex))
    (pairs : ∀ A ∈ S, AdjacentSide A) (small : S.card ≤ 1) :
    ∃ w : Face → ℕ,
      (∀ i : Fin 3, cutValue w (univ.filter fun v => v i = false) = 1) ∧
      (∀ v ∈ ring q, 1 ≤ cutValue w {v}) ∧
      (∀ A ∈ S, 1 ≤ cutValue w A) ∧ ¬IsFlower w 1 := by
  apply counterexample_same_ring q S pairs
  intro hits
  have bound := (ring_minimum_two q).2 S pairs (ring_sufficient_of_hits q S hits)
  omega

/-- Every cover admits a test family chosen from that cover alone. -/
theorem cover_aware_budget (R : Finset Vertex)
    (cover : ∀ u v, Adj u v → u ∈ R ∨ v ∈ R) :
    ∃ S : Finset (Finset Vertex), S.card ≤ 2 ∧ (∀ A ∈ S, AdjacentSide A) ∧ SufficientAt R S := by
  rcases cover_classification R cover with ⟨p, parity⟩ | ⟨q, rfl⟩
  · exact ⟨∅, by decide, by simp, parity_sufficient p parity ∅⟩
  · obtain ⟨S, size, pairs, sufficient⟩ := (ring_minimum_two q).1
    exact ⟨S, size.le, pairs, sufficient⟩

end CoverAware

