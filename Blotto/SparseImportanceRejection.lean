import Blotto.FiniteRejectionEvents

/-! A finite augmented proposal may include impossible records and infeasible
outputs. Importance is positive only where proposal probability is positive;
auxiliary fibers normalize only for positive target weights. This sparse
certificate preserves zero branches rather than assigning them false positivity. -/

namespace Blotto
open scoped BigOperators Classical

structure SparseImportanceProposal (records outputs : ℕ) where
  output : Fin records → Fin outputs
  probability : Fin records → ℝ
  importance : Fin records → ℝ
  targetWeight : Fin outputs → ℝ
  auxiliary : Fin records → ℝ
  probability_nonnegative : ∀ p, 0 ≤ probability p
  probability_sum : ∑ p, probability p = 1
  importance_nonnegative : ∀ p, 0 ≤ importance p
  importance_positive : ∀ p, 0 < probability p → 0 < importance p
  target_nonnegative : ∀ x, 0 ≤ targetWeight x
  auxiliary_nonnegative : ∀ p, 0 ≤ auxiliary p
  auxiliary_fiber_sum : ∀ x, 0 < targetWeight x →
    (∑ p, if output p = x then auxiliary p else 0) = 1
  importance_identity : ∀ p, probability p * importance p = targetWeight (output p) * auxiliary p

namespace SparseImportanceProposal

noncomputable def targetMass {r n : ℕ} (q : SparseImportanceProposal r n) : ℝ := ∑ x, q.targetWeight x

noncomputable def acceptedWeight {r n : ℕ} (q : SparseImportanceProposal r n) (bound : ℝ) (p : Fin r) : ℝ :=
  q.probability p * (q.importance p / bound)

noncomputable def acceptanceMass {r n : ℕ} (q : SparseImportanceProposal r n) (bound : ℝ) : ℝ :=
  ∑ p, q.acceptedWeight bound p

noncomputable def outputWeight {r n : ℕ} (q : SparseImportanceProposal r n) (bound : ℝ) (x : Fin n) : ℝ :=
  ∑ p, if q.output p = x then q.acceptedWeight bound p else 0

theorem acceptedWeight_identity {r n : ℕ} (q : SparseImportanceProposal r n) (bound : ℝ) (p : Fin r) :
    q.acceptedWeight bound p = q.targetWeight (q.output p) * q.auxiliary p / bound := by
  unfold acceptedWeight
  rw [← mul_div_assoc, q.importance_identity]

theorem outputWeight_eq {r n : ℕ} (q : SparseImportanceProposal r n) (bound : ℝ) (x : Fin n) :
    q.outputWeight bound x = q.targetWeight x / bound := by
  have he : q.outputWeight bound x = (q.targetWeight x / bound) *
      (∑ p, if q.output p = x then q.auxiliary p else 0) := by
    unfold outputWeight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : q.output p = x
    · rw [ite_eq_left h, ite_eq_left h, q.acceptedWeight_identity, h]
      ring
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  rw [he]
  by_cases hp : 0 < q.targetWeight x
  · rw [q.auxiliary_fiber_sum x hp, mul_one]
  · have hz : q.targetWeight x = 0 := le_antisymm (le_of_not_gt hp) (q.target_nonnegative x)
    simp [hz]

theorem acceptanceMass_eq {r n : ℕ} (q : SparseImportanceProposal r n) (bound : ℝ) :
    q.acceptanceMass bound = q.targetMass / bound := by
  have he : (∑ x, q.outputWeight bound x) = q.acceptanceMass bound := by
    unfold outputWeight acceptanceMass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    simp
  rw [← he]
  simp_rw [q.outputWeight_eq]
  simp only [div_eq_mul_inv, targetMass, Finset.sum_mul]

theorem acceptanceMass_le_one {r n : ℕ} (q : SparseImportanceProposal r n) {bound : ℝ}
    (hb : 0 < bound) (h : ∀ p, q.importance p ≤ bound) : q.acceptanceMass bound ≤ 1 := by
  calc
    q.acceptanceMass bound ≤ ∑ p, q.probability p := by
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_of_le_one_right (q.probability_nonnegative p) ((div_le_one hb).mpr (h p))
    _ = 1 := q.probability_sum

theorem conditionalOutput_eq {r n : ℕ} (q : SparseImportanceProposal r n) {bound : ℝ}
    (hb : 0 < bound) (hm : 0 < q.targetMass) (x : Fin n) :
    q.outputWeight bound x / q.acceptanceMass bound = q.targetWeight x / q.targetMass := by
  rw [q.outputWeight_eq, q.acceptanceMass_eq]
  field_simp

theorem acceptance_lower_bound {r n : ℕ} (q : SparseImportanceProposal r n) {z factor : ℝ}
    (hz : 0 < z) (hg : 0 < factor) (hLower : z ≤ q.targetMass) :
    1 / factor ≤ q.acceptanceMass (z * factor) := by
  rw [q.acceptanceMass_eq]
  have he : 1 / factor = z / (z * factor) := by field_simp
  rw [he]
  exact div_le_div_of_nonneg_right hLower (le_of_lt (mul_pos hz hg))

end SparseImportanceProposal
end Blotto
