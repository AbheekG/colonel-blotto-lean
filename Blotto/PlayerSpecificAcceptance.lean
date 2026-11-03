import Blotto.PlayerSpecificCandidate

/-! Sound acceptance of a positive cubic root and completeness of the
cubic reduction for every valid parameter pair. Actual finite enumeration
and the algebraic finite-bit implementation remain separate obligations. -/
namespace Blotto.PlayerSpecificAcceptance
open PlayerSpecificCubic PlayerSpecificCandidate
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

def partition {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂] {n : ℕ}
    (v w : Fin n → 𝕂) (gamma : 𝕂) : Fin n → Bool := fun j => decide (gamma*w j<v j)

theorem partition_respects {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂] {n : ℕ}
    (v w : Fin n → 𝕂) (gamma : 𝕂) : Respects v w (partition v w gamma) gamma := by
  intro j
  dsimp only [partition]
  by_cases h : gamma*w j<v j
  · simpa only [h,decide_true,ite_true] using h.le
  · simpa only [h,decide_false,Bool.false_eq_true,ite_false] using le_of_not_gt h

theorem count_positive {n : ℕ} (v : Values n) : 0<n := by
  by_contra h
  have hn : n=0 := Nat.eq_zero_of_not_pos h
  subst n
  have hs := v.normalized
  simp at hs

theorem endpoint_test {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂] [IsStrictOrderedRing 𝕂] {n : ℕ}
    (v w : Fin n → 𝕂) (high : Fin n → Bool) (b gamma scale : 𝕂)
    (hv : ∀ j,0<v j) (hw : ∀ j,0<w j) (hg : 0<gamma) (hs : 0<scale)
    (h : Respects v w high gamma) :
    (∀ j,PlayerSpecificMarginals.length (v j) (w j) gamma scale≤b) ↔
      ∀ j,if high j then gamma*w j≤b*scale else v j≤b*scale := by
  constructor
  · intro he j
    have hj := he j
    cases hh : high j with
    | false =>
      have hc := h j
      simp only [hh,Bool.false_eq_true,ite_false] at hc ⊢
      rw [(PlayerSpecificMarginals.low_formulas (hv j) (hw j) hg hc scale).1] at hj
      exact (div_le_iff₀ hs).mp hj
    | true =>
      have hc := h j
      simp only [hh,ite_true] at hc ⊢
      rw [(PlayerSpecificMarginals.high_formulas (hv j) (hw j) hg hc scale).1] at hj
      exact (div_le_iff₀ hs).mp hj
  · intro he j
    have hj := he j
    have hc := h j
    cases hh : high j with
    | false =>
      simp only [hh,Bool.false_eq_true,ite_false] at hj hc
      rw [(PlayerSpecificMarginals.low_formulas (hv j) (hw j) hg hc scale).1]
      exact (div_le_iff₀ hs).mpr hj
    | true =>
      simp only [hh,ite_true] at hj hc
      rw [(PlayerSpecificMarginals.high_formulas (hv j) (hw j) hg hc scale).1]
      exact (div_le_iff₀ hs).mpr hj

noncomputable def accepted {n : ℕ} (v w : Values n) (high : Fin n → Bool) (b gamma : ℝ)
    (hb : 0<b) (hb1 : b≤1) (hg : 0<gamma) (h : Respects v.weight w.weight high gamma)
    (hc : cubic (coefficients v.weight w.weight high) b gamma=0)
    (he : ∀ j,PlayerSpecificMarginals.length (v.weight j) (w.weight j) gamma
      (candidateScale (coefficients v.weight w.weight high) b gamma)≤b) : PlayerSpecificInput n where
  valuesA := v
  valuesB := w
  budget := b
  gamma := gamma
  scale := candidateScale (coefficients v.weight w.weight high) b gamma
  budget_pos := hb
  budget_le := hb1
  gamma_pos := hg
  scale_pos := scale_positive v.weight w.weight high b gamma (count_positive v) v.positive w.positive hb hg
  meanA := (candidate_means v.weight w.weight high b gamma (count_positive v) v.positive w.positive hb hg h hc).1
  meanB := (candidate_means v.weight w.weight high b gamma (count_positive v) v.positive w.positive hb hg h hc).2
  endpoint := he

theorem every_pair_is_root {n : ℕ} (i : PlayerSpecificInput n) :
    let high := partition i.valuesA.weight i.valuesB.weight i.gamma
    cubic (coefficients i.valuesA.weight i.valuesB.weight high) i.budget i.gamma=0 ∧
      i.scale=candidateScale (coefficients i.valuesA.weight i.valuesB.weight high) i.budget i.gamma :=
  (root_iff_means i.valuesA.weight i.valuesB.weight _ i.budget i.gamma i.scale i.valuesA.positive i.valuesB.positive
    i.budget_pos i.gamma_pos i.scale_pos (partition_respects _ _ _)).mp ⟨i.meanA,i.meanB⟩

theorem accepted_exact_nash {n : ℕ} (v w : Values n) (high : Fin n → Bool) (b gamma : ℝ)
    (hb : 0<b) (hb1 : b≤1) (hg : 0<gamma) (h : Respects v.weight w.weight high gamma)
    (hc : cubic (coefficients v.weight w.weight high) b gamma=0)
    (he : ∀ j,PlayerSpecificMarginals.length (v.weight j) (w.weight j) gamma
      (candidateScale (coefficients v.weight w.weight high) b gamma)≤b) :
    let i := accepted v w high b gamma hb hb1 hg h hc he
    Supported 1 i.lawA ∧ Supported b i.lawB ∧ regret v 1 i.lawA i.lawB=0 ∧ regret w b i.lawB i.lawA=0 := by
  let i := accepted v w high b gamma hb hb1 hg h hc he
  have hn := PlayerSpecificEquilibrium.exact_nash i
  exact ⟨i.lawA_supported,i.lawB_supported,hn.1,hn.2.1⟩

end Blotto.PlayerSpecificAcceptance
