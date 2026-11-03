import Blotto.GeneralPaperFourAverageAlgebra

/-! The averaged four-regret CDF-distance inequality and its empirical-row
game-gap consequence. Fixed signed maximizers are chosen after averaging.
The concrete source must supply its own regret and optimizer residuals.
-/
namespace Blotto.GeneralPaperFourAverageGap
open scoped BigOperators
open GeneralPaperCodeCDF GeneralPaperSignedPairing GeneralPaperCodeCDFDistance GeneralPaperCodeAverages
open GeneralPaperFourAverageAlgebra
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def weightedPayoff {m n : ℕ} (v : Fin m → ℝ) (p q : Fin m → Fin n → ℝ) : ℝ :=
  ∑ j, v j*codePayoff (p j) (q j)

noncomputable def weightedDistance {m n : ℕ} (hn : 0<n) (v : Fin m → ℝ) (p q : Fin m → Fin n → ℝ) : ℝ :=
  ∑ j, v j*distance hn (p j) (q j)

noncomputable def maximizingX {m n : ℕ} (hn : 0<n) (tr : Trajectory m n) (T : ℕ) (j : Fin m) : Fin (n+n) → ℝ :=
  maximizing hn (fun a => cdf (meanP tr T j) a-cdf (meanX tr T j) a)

noncomputable def maximizingY {m n : ℕ} (hn : 0<n) (tr : Trajectory m n) (T : ℕ) (j : Fin m) : Fin (n+n) → ℝ :=
  maximizing hn (fun a => cdf (meanQ tr T j) a-cdf (meanY tr T j) a)

theorem maximizingX_probability {m n : ℕ} (hn : 0<n) (tr : Trajectory m n) (T : ℕ) (j : Fin m) :
    Probability (maximizingX hn tr T j) := maximizing_probability hn _

theorem maximizingY_probability {m n : ℕ} (hn : 0<n) (tr : Trajectory m n) (T : ℕ) (j : Fin m) :
    Probability (maximizingY hn tr T j) := maximizing_probability hn _

theorem average_core_max {m n : ℕ} (hn : 0<n) (tr : Trajectory m n) (v : Fin m → ℝ) (T : ℕ)
    (x y : Fin m → Fin n → ℝ) :
    averageCore tr v T x y (maximizingX hn tr T) (maximizingY hn tr T)=
      weightedPayoff v (meanP tr T) y-weightedPayoff v x (meanQ tr T)+
        weightedDistance hn v (meanP tr T) (meanX tr T)+weightedDistance hn v (meanQ tr T) (meanY tr T) := by
  unfold averageCore weightedPayoff weightedDistance maximizingX maximizingY distance
  simp only [maximizing_pair,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]

theorem four_regret {m n : ℕ} (hn : 0<n) (tr : Trajectory m n) (v : Fin m → ℝ) (T : ℕ) (hT : 0<T)
    (x y : Fin m → Fin n → ℝ) (hy : ∀ j, ∑ a, y j a=1)
    (hq : ∀ t<T, ∀ j, ∑ a, tr.q t j a=1) (beta slack : ℝ)
    (hRegret : ∀ testLambda testMu, (∀ j, Probability (testLambda j)) → (∀ j, Probability (testMu j)) →
      regretMean tr v T x y testLambda testMu+2*beta<slack)
    (hX : ∀ t<T, -beta≤∑ j, v j*residualX tr x t j)
    (hY : ∀ t<T, -beta≤∑ j, v j*residualY tr y t j) :
    weightedPayoff v (meanP tr T) y-weightedPayoff v x (meanQ tr T)+
      weightedDistance hn v (meanP tr T) (meanX tr T)+weightedDistance hn v (meanQ tr T) (meanY tr T)<slack := by
  have hr := hRegret (maximizingX hn tr T) (maximizingY hn tr T)
    (maximizingX_probability hn tr T) (maximizingY_probability hn tr T)
  have hc := average_cancellation tr v T x y (maximizingX hn tr T) (maximizingY hn tr T) hq hy
  have hx := average_lower T hT (fun t => ∑ j, v j*residualX tr x t j) (-beta) hX
  have hy' := average_lower T hT (fun t => ∑ j, v j*residualY tr y t j) (-beta) hY
  rw [average_core_max] at hc
  linarith only [hr,hc,hx,hy']

theorem weighted_payoff_left {m n : ℕ} (hn : 0<n) (v : Fin m → ℝ) (hv : ∀ j, 0≤v j)
    (p x q : Fin m → Fin n → ℝ) (hq : ∀ j, Probability (q j)) :
    weightedPayoff v x q-weightedPayoff v p q≤weightedDistance hn v p x := by
  unfold weightedPayoff weightedDistance
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have he := (abs_le.mp (GeneralPaperCodeCDFDistance.payoff_left hn (p j) (x j) (q j) (hq j))).1
  have hm := mul_le_mul_of_nonneg_left (show codePayoff (x j) (q j)-codePayoff (p j) (q j)≤distance hn (p j) (x j) by linarith only [he]) (hv j)
  nlinarith only [hm]

theorem weighted_payoff_right {m n : ℕ} (hn : 0<n) (v : Fin m → ℝ) (hv : ∀ j, 0≤v j)
    (p q y : Fin m → Fin n → ℝ) (hp : ∀ j, Probability (p j))
    (hq : ∀ j, Probability (q j)) (hy : ∀ j, Probability (y j)) :
    weightedPayoff v p q-weightedPayoff v p y≤weightedDistance hn v q y := by
  unfold weightedPayoff weightedDistance
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have he := (abs_le.mp (GeneralPaperCodeCDFDistance.payoff_right hn (p j) (q j) (y j) (hp j) (hq j) (hy j))).2
  have hm := mul_le_mul_of_nonneg_left he (hv j)
  nlinarith only [hm]

theorem empirical_gap {m n : ℕ} (hn : 0<n) (tr : Trajectory m n) (v : Fin m → ℝ) (hv : ∀ j, 0≤v j)
    (T : ℕ) (hT : 0<T) (x y : Fin m → Fin n → ℝ) (hx : ∀ j, Probability (x j)) (hy : ∀ j, Probability (y j))
    (hq : ∀ t<T, ∀ j, Probability (tr.q t j)) (beta slack : ℝ)
    (hRegret : ∀ testLambda testMu, (∀ j, Probability (testLambda j)) → (∀ j, Probability (testMu j)) →
      regretMean tr v T x y testLambda testMu+2*beta<slack)
    (hX : ∀ t<T, -beta≤∑ j, v j*residualX tr x t j)
    (hY : ∀ t<T, -beta≤∑ j, v j*residualY tr y t j) :
    weightedPayoff v (meanX tr T) y-weightedPayoff v x (meanY tr T)<slack := by
  have hg := four_regret hn tr v T hT x y (fun j => (hy j).2) (fun t ht j => (hq t ht j).2) beta slack hRegret hX hY
  have hl := weighted_payoff_left hn v hv (meanP tr T) (meanX tr T) y hy
  have hr := weighted_payoff_right hn v hv x (meanQ tr T) (meanY tr T) hx
    (fun j => mean_probability T hT (fun t => tr.q t j) (fun t ht => hq t ht j))
    (fun j => empirical_probability T hT (fun t => tr.rowY t j))
  linarith only [hg,hl,hr]

end Blotto.GeneralPaperFourAverageGap
