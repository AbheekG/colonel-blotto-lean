import Blotto.ProductSecurityTrainerGap

/-! An explicit conservative rational round count realizes the source small
expected-gap target for the exact finite trainer. The entropy upper bound is
an input certificate; native training-error and continuous-output joins remain. -/

namespace Blotto
open scoped BigOperators Classical
namespace ProductSecurityTrainer

noncomputable def meanGap {m : ℕ} (c : ProductSecurityTrainer m) (T : ℕ) : ℝ :=
  SparseMW.historyMean c.transition T (fun past =>
    FiniteSaddle.GapAt c.matrix (FiniteSaddle.historyAverage (fun h => (c.lawA h).realWeight) past)
      (FiniteSaddle.historyAverage (fun h => (c.lawB h).realWeight) past)
      (FiniteSaddle.minimizingRow c.actionsA_positive c.matrix
        (FiniteSaddle.historyAverage (fun h => (c.lawB h).realWeight) past))
      (FiniteSaddle.maximizingColumn c.actionsB_positive c.matrix
        (FiniteSaddle.historyAverage (fun h => (c.lawA h).realWeight) past)))

def trainingRounds (eta epsilon entropy : ℚ) : ℕ :=
  max 1 (rationalFactorCeiling (4096 * entropy / (eta * epsilon)))

theorem trainingRounds_positive (eta epsilon entropy : ℚ) : 0 < trainingRounds eta epsilon entropy := by
  unfold trainingRounds
  omega

theorem trainingRounds_guard (eta epsilon entropy : ℚ) (heta : 0 < eta) (he : 0 < epsilon)
    (hJ : 0 ≤ entropy) :
    4096 * entropy ≤ (trainingRounds eta epsilon entropy : ℚ) * eta * epsilon := by
  have hc := rationalFactorCeiling_bound (4096 * entropy / (eta * epsilon)) (by positivity)
  have hm : rationalFactorCeiling (4096 * entropy / (eta * epsilon)) ≤ trainingRounds eta epsilon entropy :=
    Nat.le_max_right _ _
  have hmr : (rationalFactorCeiling (4096 * entropy / (eta * epsilon)) : ℚ) ≤ trainingRounds eta epsilon entropy := by exact_mod_cast hm
  have hg := (div_le_iff₀ (mul_pos heta he)).mp (hc.trans hmr)
  convert hg using 1
  ring

theorem scheduled_expected_gap {m : ℕ} (c : ProductSecurityTrainer m) (epsilon entropy : ℚ)
    (he : 0 < epsilon ∧ epsilon ≤ 1) (hJ : 0 ≤ entropy)
    (hEntropy : Real.log c.actionsA + Real.log c.actionsB ≤ (entropy : ℝ))
    (hEta : c.eta = epsilon / 2048) (hTheta : c.theta = c.eta * epsilon / 32768) :
    c.meanGap (trainingRounds c.eta epsilon entropy) ≤ (epsilon : ℝ) / 128 := by
  let T := trainingRounds c.eta epsilon entropy
  have hetaR : (0 : ℝ) < (c.eta : ℝ) := by exact_mod_cast c.eta_unit.1
  have hTR : (0 : ℝ) < T := by exact_mod_cast trainingRounds_positive c.eta epsilon entropy
  have he0 : (0 : ℝ) < (epsilon : ℝ) := by exact_mod_cast he.1
  have he1 : (epsilon : ℝ) ≤ 1 := by exact_mod_cast he.2
  have hEtaR : (c.eta : ℝ) = (epsilon : ℝ) / 2048 := by exact_mod_cast hEta
  have hThetaR : (c.theta : ℝ) = (c.eta : ℝ) * (epsilon : ℝ) / 32768 := by exact_mod_cast hTheta
  have hguard : (4096 : ℝ) * (entropy : ℝ) ≤ (T : ℝ) * (c.eta : ℝ) * (epsilon : ℝ) := by
    exact_mod_cast trainingRounds_guard c.eta epsilon entropy c.eta_unit.1 he.1 hJ
  have herror : 0 ≤ 3 * (c.theta : ℝ) / (c.eta : ℝ) ∧ 3 * (c.theta : ℝ) / (c.eta : ℝ) ≤ 1 := by
    rw [hThetaR]
    have hcancel : 3 * ((c.eta : ℝ) * (epsilon : ℝ) / 32768) / (c.eta : ℝ) = 3 * (epsilon : ℝ) / 32768 := by field_simp
    rw [hcancel]
    constructor <;> linarith
  have hquad : (1 + 3 * (c.theta : ℝ) / (c.eta : ℝ)) ^ 2 + 1 ≤ 5 := by nlinarith [herror.1,herror.2]
  have hMoment := mul_le_mul_of_nonneg_left hquad (show (0 : ℝ) ≤ (c.eta : ℝ) ^ 2 * T by positivity)
  have heGap := c.expected_gap T
  change (c.eta : ℝ) * (T : ℝ) * c.meanGap T ≤ _ at heGap
  have hmain : (c.eta : ℝ) * T * c.meanGap T ≤ (c.eta : ℝ) * T * ((epsilon : ℝ) / 128) := by
    have hbudget : 2 * (entropy : ℝ) ≤ (c.eta : ℝ) * T * ((epsilon : ℝ) / 2048) := by nlinarith [hguard]
    have hcost : (c.eta : ℝ) ^ 2 * T * 5 + 6 * (c.theta : ℝ) * T ≤
        (c.eta : ℝ) * T * (6 * (epsilon : ℝ) / 2048) := by
      rw [hThetaR]
      rw [hEtaR]
      nlinarith
    have hscale : (c.eta : ℝ) * T * ((epsilon : ℝ) / 2048 + 6 * (epsilon : ℝ) / 2048) ≤
        (c.eta : ℝ) * T * ((epsilon : ℝ) / 128) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (mul_pos hetaR hTR).le
    nlinarith [heGap,hMoment,hbudget,hcost,hscale,hEntropy]
  exact (mul_le_mul_iff_of_pos_left (mul_pos hetaR hTR)).mp hmain

def withAccuracy {m : ℕ} (c : ProductSecurityTrainer m) (epsilon : ℚ)
    (he : 0 < epsilon ∧ epsilon ≤ 1) : ProductSecurityTrainer m :=
  { c with
    eta := epsilon / 2048
    theta := (epsilon / 2048) * epsilon / 32768
    eta_unit := by constructor <;> linarith [he.1,he.2]
    theta_unit := by
      constructor
      · exact div_pos (mul_pos (div_pos he.1 (by norm_num)) he.1) (by norm_num)
      · have hSquare : epsilon * epsilon ≤ 1 := (mul_le_mul he.2 he.2 he.1.le (by norm_num)).trans_eq (by norm_num)
        nlinarith }

theorem withAccuracy_expected_gap {m : ℕ} (c : ProductSecurityTrainer m) (epsilon entropy : ℚ)
    (he : 0 < epsilon ∧ epsilon ≤ 1) (hJ : 0 ≤ entropy)
    (hEntropy : Real.log c.actionsA + Real.log c.actionsB ≤ (entropy : ℝ)) :
    (c.withAccuracy epsilon he).meanGap (trainingRounds (epsilon / 2048) epsilon entropy) ≤ (epsilon : ℝ) / 128 := by
  exact scheduled_expected_gap (c.withAccuracy epsilon he) epsilon entropy he hJ hEntropy rfl rfl

end ProductSecurityTrainer
end Blotto
