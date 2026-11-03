import Blotto.WeightedGuideTree

/-! Exact rejection on a finite augmented record space. The importance identity
and auxiliary-kernel normalization are explicit certificates to be established
by a proposal implementation; no marginal proposal density is required. -/

namespace Blotto
open scoped BigOperators Classical

structure FiniteImportanceProposal (records outputs : ℕ) where
  output : Fin records → Fin outputs
  probability : Fin records → ℝ
  importance : Fin records → ℝ
  targetWeight : Fin outputs → ℝ
  auxiliary : Fin records → ℝ
  probability_nonnegative : ∀ p, 0 ≤ probability p
  probability_sum : ∑ p, probability p = 1
  importance_positive : ∀ p, 0 < importance p
  target_nonnegative : ∀ x, 0 ≤ targetWeight x
  auxiliary_nonnegative : ∀ p, 0 ≤ auxiliary p
  auxiliary_fiber_sum : ∀ x, (∑ p, if output p = x then auxiliary p else 0) = 1
  importance_identity : ∀ p, probability p * importance p = targetWeight (output p) * auxiliary p

namespace FiniteImportanceProposal

noncomputable def targetMass {r n : ℕ} (q : FiniteImportanceProposal r n) : ℝ :=
  ∑ x, q.targetWeight x

noncomputable def acceptedWeight {r n : ℕ} (q : FiniteImportanceProposal r n) (bound : ℝ) (p : Fin r) : ℝ :=
  q.probability p * (q.importance p / bound)

noncomputable def acceptanceMass {r n : ℕ} (q : FiniteImportanceProposal r n) (bound : ℝ) : ℝ :=
  ∑ p, q.acceptedWeight bound p

noncomputable def acceptedOutputWeight {r n : ℕ} (q : FiniteImportanceProposal r n) (bound : ℝ) (x : Fin n) : ℝ :=
  ∑ p, if q.output p = x then q.acceptedWeight bound p else 0

theorem importance_coin_valid {r n : ℕ} (q : FiniteImportanceProposal r n) {bound : ℝ}
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) (p : Fin r) :
    0 < q.importance p / bound ∧ q.importance p / bound ≤ 1 := by
  constructor
  · exact div_pos (q.importance_positive p) hb
  · exact (div_le_one hb).mpr (h p)

theorem acceptedWeight_nonnegative {r n : ℕ} (q : FiniteImportanceProposal r n) {bound : ℝ}
    (hb : 0 < bound) (p : Fin r) : 0 ≤ q.acceptedWeight bound p :=
  mul_nonneg (q.probability_nonnegative p) (le_of_lt (div_pos (q.importance_positive p) hb))

theorem acceptedWeight_identity {r n : ℕ} (q : FiniteImportanceProposal r n) (bound : ℝ) (p : Fin r) :
    q.acceptedWeight bound p = q.targetWeight (q.output p) * q.auxiliary p / bound := by
  unfold acceptedWeight
  rw [← mul_div_assoc, q.importance_identity]

theorem acceptedOutputWeight_eq {r n : ℕ} (q : FiniteImportanceProposal r n) (bound : ℝ) (x : Fin n) :
    q.acceptedOutputWeight bound x = q.targetWeight x / bound := by
  unfold acceptedOutputWeight
  have he : ∀ p, (if q.output p = x then q.acceptedWeight bound p else 0) =
      (q.targetWeight x / bound) * (if q.output p = x then q.auxiliary p else 0) := by
    intro p
    by_cases h : q.output p = x
    · rw [ite_eq_left h, ite_eq_left h, q.acceptedWeight_identity, h]
      ring
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  simp_rw [he]
  rw [← Finset.mul_sum, q.auxiliary_fiber_sum, mul_one]

theorem acceptanceMass_eq {r n : ℕ} (q : FiniteImportanceProposal r n) (bound : ℝ) :
    q.acceptanceMass bound = q.targetMass / bound := by
  have he : (∑ x, q.acceptedOutputWeight bound x) = q.acceptanceMass bound := by
    unfold acceptedOutputWeight acceptanceMass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    simp
  rw [← he]
  simp_rw [q.acceptedOutputWeight_eq]
  simp only [div_eq_mul_inv, targetMass, Finset.sum_mul]

theorem acceptanceMass_le_one {r n : ℕ} (q : FiniteImportanceProposal r n) {bound : ℝ}
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) : q.acceptanceMass bound ≤ 1 := by
  calc
    q.acceptanceMass bound ≤ ∑ p, q.probability p := by
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_of_le_one_right (q.probability_nonnegative p) (q.importance_coin_valid hb h p).2
    _ = 1 := q.probability_sum

theorem acceptanceMass_positive {r n : ℕ} (q : FiniteImportanceProposal r n) {bound : ℝ}
    (hb : 0 < bound) (hm : 0 < q.targetMass) : 0 < q.acceptanceMass bound := by
  rw [q.acceptanceMass_eq]
  exact div_pos hm hb

theorem conditionalOutput_eq {r n : ℕ} (q : FiniteImportanceProposal r n) {bound : ℝ}
    (hb : 0 < bound) (hm : 0 < q.targetMass) (x : Fin n) :
    q.acceptedOutputWeight bound x / q.acceptanceMass bound = q.targetWeight x / q.targetMass := by
  rw [q.acceptedOutputWeight_eq, q.acceptanceMass_eq]
  field_simp

theorem targetMass_le_bound {r n : ℕ} (q : FiniteImportanceProposal r n) {bound : ℝ}
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) : q.targetMass ≤ bound := by
  have he := q.acceptanceMass_le_one hb h
  rw [q.acceptanceMass_eq] at he
  exact (div_le_one hb).mp he

theorem acceptance_lower_bound {r n : ℕ} (q : FiniteImportanceProposal r n) {z factor : ℝ}
    (hz : 0 < z) (hg : 0 < factor) (hLower : z ≤ q.targetMass) :
    1 / factor ≤ q.acceptanceMass (z * factor) := by
  rw [q.acceptanceMass_eq]
  have he : 1 / factor = z / (z * factor) := by field_simp
  rw [he]
  exact div_le_div_of_nonneg_right hLower (le_of_lt (mul_pos hz hg))

end FiniteImportanceProposal
end Blotto
