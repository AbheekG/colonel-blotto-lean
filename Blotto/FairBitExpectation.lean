import Blotto.AverageFairBits

/-! Exact expectation identities for fresh fair bit vectors. Splitting off
the first bit exposes the independent remaining vector used by digit loops. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

noncomputable def headTailEquiv (K : ℕ) : (Bool × (Fin K → Bool)) ≃ (Fin (K + 1) → Bool) where
  toFun := fun x => prependBit x.1 x.2
  invFun := fun bits => (bits 0, Fin.tail bits)
  left_inv := by rintro ⟨b, tail⟩; simp [prependBit]
  right_inv := fun bits => Fin.cons_self_tail bits

theorem fairBitLaw_integral_mean (K : ℕ) (f : (Fin K → Bool) → ℝ) :
    (∫ bits, f bits ∂(fairBitLaw K : Measure (Fin K → Bool))) =
      (1 / (2 : ℝ) ^ K) * ∑ bits, f bits := by
  rw [integral_fintype Integrable.of_finite]
  simp only [Measure.real, fairBitLaw_singleton_realWeight,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (2 : ℝ) ^ K), smul_eq_mul, ← Finset.mul_sum]

theorem fairBitLaw_integral_split (K : ℕ) (f : (Fin (K + 1) → Bool) → ℝ) :
    (∫ bits, f bits ∂(fairBitLaw (K + 1) : Measure (Fin (K + 1) → Bool))) =
      (1 / 2 : ℝ) * (∫ bits, f (prependBit false bits) ∂(fairBitLaw K : Measure (Fin K → Bool))) +
      (1 / 2 : ℝ) * (∫ bits, f (prependBit true bits) ∂(fairBitLaw K : Measure (Fin K → Bool))) := by
  rw [fairBitLaw_integral_mean, fairBitLaw_integral_mean, fairBitLaw_integral_mean]
  rw [← Equiv.sum_comp (headTailEquiv K) f, Fintype.sum_prod_type, Fintype.sum_bool]
  change 1 / (2 : ℝ) ^ (K + 1) *
    ((∑ bits, f (prependBit true bits)) + (∑ bits, f (prependBit false bits))) = _
  rw [pow_succ]
  field_simp
  ring

end Blotto
