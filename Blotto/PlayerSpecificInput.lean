import Blotto.PlayerSpecificMarginals

/-! Accepted player-specific parameters construct two actual whole-allocation
couplings with the paper's marginals and hard budgets. Acceptance/recognition
and the incentive proof are separate components. -/
namespace Blotto
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false

structure PlayerSpecificInput (n : ℕ) where
  valuesA : Values n
  valuesB : Values n
  budget : ℝ
  gamma : ℝ
  scale : ℝ
  budget_pos : 0<budget
  budget_le : budget≤1
  gamma_pos : 0<gamma
  scale_pos : 0<scale
  meanA : (∑ j,PlayerSpecificMarginals.probA (valuesA.weight j) (valuesB.weight j) gamma*
    PlayerSpecificMarginals.length (valuesA.weight j) (valuesB.weight j) gamma scale)=2
  meanB : (∑ j,PlayerSpecificMarginals.probB (valuesA.weight j) (valuesB.weight j) gamma*
    PlayerSpecificMarginals.length (valuesA.weight j) (valuesB.weight j) gamma scale)=2*budget
  endpoint : ∀ j,PlayerSpecificMarginals.length (valuesA.weight j) (valuesB.weight j) gamma scale≤budget

namespace PlayerSpecificInput
noncomputable def length {n : ℕ} (i : PlayerSpecificInput n) (j : Fin n) : ℝ :=
  PlayerSpecificMarginals.length (i.valuesA.weight j) (i.valuesB.weight j) i.gamma i.scale

noncomputable def probA {n : ℕ} (i : PlayerSpecificInput n) (j : Fin n) : ℝ :=
  PlayerSpecificMarginals.probA (i.valuesA.weight j) (i.valuesB.weight j) i.gamma

noncomputable def probB {n : ℕ} (i : PlayerSpecificInput n) (j : Fin n) : ℝ :=
  PlayerSpecificMarginals.probB (i.valuesA.weight j) (i.valuesB.weight j) i.gamma

theorem length_pos {n : ℕ} (i : PlayerSpecificInput n) (j : Fin n) : 0 < i.length j :=
  PlayerSpecificMarginals.length_pos (i.valuesA.positive j) (i.valuesB.positive j) i.gamma_pos i.scale_pos

theorem probA_bounds {n : ℕ} (i : PlayerSpecificInput n) (j : Fin n) : 0 < i.probA j ∧ i.probA j≤1 :=
  ⟨PlayerSpecificMarginals.probA_pos (i.valuesA.positive j) (i.valuesB.positive j) i.gamma_pos,
    PlayerSpecificMarginals.probA_le_one _ _ _⟩

theorem probB_bounds {n : ℕ} (i : PlayerSpecificInput n) (j : Fin n) : 0 < i.probB j ∧ i.probB j≤1 :=
  ⟨PlayerSpecificMarginals.probB_pos (i.valuesA.positive j) (i.valuesB.positive j) i.gamma_pos,
    PlayerSpecificMarginals.probB_le_one _ _ _⟩

noncomputable def systemA {n : ℕ} (i : PlayerSpecificInput n) : LottoResourceSystem n where
  B := 1
  length := i.length
  initial := fun j => i.probA j*i.length j
  B_pos := by norm_num
  length_pos := i.length_pos
  length_le := fun j => (i.endpoint j).trans i.budget_le
  initial_box := fun j => ⟨mul_nonneg (i.probA_bounds j).1.le (i.length_pos j).le,
    (mul_le_mul_of_nonneg_right (i.probA_bounds j).2 (i.length_pos j).le).trans_eq (one_mul _)⟩
  initial_sum := by simpa only [probA,length,mul_one] using i.meanA

noncomputable def systemB {n : ℕ} (i : PlayerSpecificInput n) : LottoResourceSystem n where
  B := i.budget
  length := i.length
  initial := fun j => i.probB j*i.length j
  B_pos := i.budget_pos
  length_pos := i.length_pos
  length_le := i.endpoint
  initial_box := fun j => ⟨mul_nonneg (i.probB_bounds j).1.le (i.length_pos j).le,
    (mul_le_mul_of_nonneg_right (i.probB_bounds j).2 (i.length_pos j).le).trans_eq (one_mul _)⟩
  initial_sum := i.meanB

noncomputable def lawA {n : ℕ} (i : PlayerSpecificInput n) : Mixed n := i.systemA.law
noncomputable def lawB {n : ℕ} (i : PlayerSpecificInput n) : Mixed n := i.systemB.law

theorem lawA_budget {n : ℕ} (i : PlayerSpecificInput n) :
    ∀ᵐ x ∂(i.lawA : Measure (Allocation n)),FullBudget 1 x := i.systemA.law_contract.1

theorem lawB_budget {n : ℕ} (i : PlayerSpecificInput n) :
    ∀ᵐ x ∂(i.lawB : Measure (Allocation n)),FullBudget i.budget x := i.systemB.law_contract.1

theorem lawA_supported {n : ℕ} (i : PlayerSpecificInput n) : Supported 1 i.lawA := i.systemA.law_supported

theorem lawB_supported {n : ℕ} (i : PlayerSpecificInput n) : Supported i.budget i.lawB := i.systemB.law_supported

theorem lawA_marginal {n : ℕ} (i : PlayerSpecificInput n) (j : Fin n) :
    (marginal i.lawA j : Measure ℝ)=zeroUniformLaw (i.length j) (i.probA j) := by
  rw [lawA,i.systemA.law_zeroUniform j]
  change zeroUniformLaw (i.length j) ((i.probA j*i.length j)/i.length j)=_
  rw [mul_div_cancel_right₀ _ (i.length_pos j).ne']

theorem lawB_marginal {n : ℕ} (i : PlayerSpecificInput n) (j : Fin n) :
    (marginal i.lawB j : Measure ℝ)=zeroUniformLaw (i.length j) (i.probB j) := by
  rw [lawB,i.systemB.law_zeroUniform j]
  change zeroUniformLaw (i.length j) ((i.probB j*i.length j)/i.length j)=_
  rw [mul_div_cancel_right₀ _ (i.length_pos j).ne']

end PlayerSpecificInput
end Blotto
