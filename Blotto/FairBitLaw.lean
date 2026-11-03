import Blotto.BitIndex
import Blotto.RealCDFDistance

/-! Actual law of K independent fair Boolean inputs. Each recursive step
chooses a fresh fair head independently of the remaining input vector. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def booleanVectorPointLaw {K : ℕ} (x : Fin K → Bool) : ProbabilityMeasure (Fin K → Bool) :=
  ⟨Measure.dirac x, inferInstance⟩

def prependBit {K : ℕ} (b : Bool) (tail : Fin K → Bool) : Fin (K + 1) → Bool := Fin.cons b tail

noncomputable def fairBitLaw : (K : ℕ) → ProbabilityMeasure (Fin K → Bool)
  | 0 => booleanVectorPointLaw (fun j => Fin.elim0 j)
  | K + 1 => probabilityMixture (fun _ : Fin 2 => 1 / 2)
      ![(fairBitLaw K).map (prependBit false), (fairBitLaw K).map (prependBit true)]
      (by intro i; norm_num) (by simp)

theorem cons_preimage_singleton {K : ℕ} (b : Bool) (x : Fin (K + 1) → Bool) :
    (prependBit b : (Fin K → Bool) → (Fin (K + 1) → Bool)) ⁻¹' {x} =
      if x 0 = b then {Fin.tail x} else ∅ := by
  by_cases hb : x 0 = b
  · rw [ite_eq_left hb]
    ext y
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro he
      funext j
      have hv := congrArg (fun f : Fin (K + 1) → Bool => f j.succ) he
      simpa only [prependBit, Fin.cons_succ, Fin.tail] using hv
    · intro he
      subst y
      change Fin.cons b (Fin.tail x) = x
      rw [← hb, Fin.cons_self_tail]
  · rw [ite_eq_right hb]
    ext y
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    intro he
    apply hb
    exact (congrArg (fun z => z 0) he).symm

theorem fairBitLaw_singleton (K : ℕ) (x : Fin K → Bool) :
    (fairBitLaw K : Measure (Fin K → Bool)) {x} = (ENNReal.ofReal (1 / 2)) ^ K := by
  induction K with
  | zero =>
    have hx : x = fun j => Fin.elim0 j := by funext j; exact Fin.elim0 j
    simp [fairBitLaw, booleanVectorPointLaw, hx]
  | succ K ih =>
    have hf (b : Bool) :
        (Measure.map (prependBit b) (fairBitLaw K : Measure (Fin K → Bool))) {x} =
          if x 0 = b then (ENNReal.ofReal (1 / 2)) ^ K else 0 := by
      rw [Measure.map_apply (measurable_of_countable (prependBit b)) (measurableSet_singleton x), cons_preimage_singleton]
      split_ifs
      · exact ih _
      · exact measure_empty
    change (mixtureMeasure (fun _ : Fin 2 => (1 / 2 : ℝ))
      ![(fairBitLaw K).map (prependBit false), (fairBitLaw K).map (prependBit true)]) {x} = _
    rw [mixtureMeasure, Measure.sum_apply _ (measurableSet_singleton x), tsum_fintype]
    simp only [Fin.sum_univ_succ, Measure.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.univ_unique, Finset.sum_singleton]
    change ENNReal.ofReal (1 / 2) * (Measure.map (prependBit false) (fairBitLaw K : Measure (Fin K → Bool))) {x} +
      ENNReal.ofReal (1 / 2) * (Measure.map (prependBit true) (fairBitLaw K : Measure (Fin K → Bool))) {x} = _
    rw [hf false, hf true]
    cases x 0 <;> simp [pow_succ, mul_comm]

theorem fairBitLaw_singleton_realWeight (K : ℕ) (x : Fin K → Bool) :
    (fairBitLaw K : Measure (Fin K → Bool)) {x} = ENNReal.ofReal (1 / (2 : ℝ) ^ K) := by
  rw [fairBitLaw_singleton, ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2), one_div_pow]

end Blotto
