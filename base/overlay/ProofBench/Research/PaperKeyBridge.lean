import ProofBench.Research.PaperKeySpec
import ProofBench.Research.KeyCornerLemma

/-! Correspondence between an independently stated graph specification and the
constructed proof. The strict-order assumption also covers order zero. -/

namespace PaperCorner

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem crosses_iff (r s : G.Separation) :
    Crosses r s ↔ CornerSection.Cross r s := by
  unfold Crosses CornerSection.Cross CornerSection.Nested CornerSection.OrientedBelow
  simp only [Bool.exists_bool, CubicalDiagrams.side, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true]
  tauto

omit [Fintype V] in
private theorem pair_sets {u v a b : Finset V}
    (h : ({u, v} : Finset (Finset V)) = {a, b}) :
    (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  have mem (x : Finset V) : (x = u ∨ x = v) ↔ (x = a ∨ x = b) := by
    simpa only [mem_insert, mem_singleton] using (Finset.ext_iff.mp h x)
  have hu := mem u
  have hv := mem v
  have ha := mem a
  have hb := mem b
  grind only

private theorem uniform_from_graph {D : Fin 3 → G.Separation}
    (h : CornerSection.UniformlyCrossing D) : Uniform D := by
  intro i
  obtain ⟨P, ⟨s, hs⟩, allCrossers⟩ := h i
  let r := D i
  obtain ⟨cover, cl, cr, lr⟩ := CornerSection.partition_parts r s
  refine ⟨_, _, _, cover, cl, cr, lr, ?_⟩
  intro j cross
  have eq := (allCrossers j ((crosses_iff _ _).mp cross)).trans hs.symm
  have ce := congrArg Prod.fst eq
  have li := congrArg Prod.snd eq
  exact ⟨ce, pair_sets li⟩

private theorem uniform_at_zero {D : Fin 3 → G.Separation}
    (orders : ∀ i, (D i).order = 0) : Uniform D := by
  intro i
  have empty : (D i).separator = ∅ := Finset.card_eq_zero.mp (orders i)
  refine ⟨∅, ∅, ∅, ?_, by simp, by simp, by simp, ?_⟩
  · simp [empty]
  · intro j _
    simp [Induces, empty]

/-- Finite-graph version of the source paper's Key Lemma 4.14. -/
theorem key_lemma_4_14 (D : Fin 3 → G.Separation) (q k : ℕ)
    (unbreakable : UnbreakableBelow G q k) (orders : ∀ i, (D i).order = k)
    (equity : Equitable D k) (criss : CrissCompatible D (2 * q + k)) :
    Uniform D := by
  cases k with
  | zero => exact uniform_at_zero orders
  | succ k =>
    apply uniform_from_graph
    apply CornerSection.key_lemma_4_14 D q (k + 1) _ orders
    · intro i j cross a b
      have h := equity i j ((crosses_iff _ _).mpr cross) a b
      cases a <;> cases b <;> exact h
    · intro i j cross a b
      have h := criss i j ((crosses_iff _ _).mpr cross) a b
      cases a <;> cases b <;> exact h
    · intro s ord
      exact unbreakable s (by omega)

end PaperCorner
