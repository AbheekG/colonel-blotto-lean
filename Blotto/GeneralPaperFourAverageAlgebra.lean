import Blotto.GeneralPaperCodeAverages

/-! Average the exact four-loss cancellation with fixed comparator
marginals and signed multipliers. All arrays here are analysis histories;
the concrete source is instantiated separately with its own execution.
-/
namespace Blotto.GeneralPaperFourAverageAlgebra
open scoped BigOperators
open GeneralPaperCodeCDF GeneralPaperSignedPairing GeneralPaperFourLossAlgebra GeneralPaperCodeAverages
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Trajectory (m n : ℕ) where
  p : ℕ → Fin m → Fin n → ℝ
  q : ℕ → Fin m → Fin n → ℝ
  lambda : ℕ → Fin m → Fin (n+n) → ℝ
  mu : ℕ → Fin m → Fin (n+n) → ℝ
  rowX : ℕ → Fin m → Fin n
  rowY : ℕ → Fin m → Fin n

noncomputable def meanP {m n : ℕ} (tr : Trajectory m n) (T : ℕ) (j : Fin m) : Fin n → ℝ := mean T (fun t => tr.p t j)
noncomputable def meanQ {m n : ℕ} (tr : Trajectory m n) (T : ℕ) (j : Fin m) : Fin n → ℝ := mean T (fun t => tr.q t j)
noncomputable def meanX {m n : ℕ} (tr : Trajectory m n) (T : ℕ) (j : Fin m) : Fin n → ℝ := empirical T (fun t => tr.rowX t j)
noncomputable def meanY {m n : ℕ} (tr : Trajectory m n) (T : ℕ) (j : Fin m) : Fin n → ℝ := empirical T (fun t => tr.rowY t j)

noncomputable def core {m n : ℕ} (tr : Trajectory m n) (x y : Fin m → Fin n → ℝ)
    (testLambda testMu : Fin m → Fin (n+n) → ℝ) (t : ℕ) (j : Fin m) : ℝ :=
  codePayoff (tr.p t j) (y j)-codePayoff (x j) (tr.q t j)+
    pair (testLambda j) (fun a => cdf (tr.p t j) a-rowCDF (tr.rowX t j) a)+
    pair (testMu j) (fun a => cdf (tr.q t j) a-rowCDF (tr.rowY t j) a)

def residualX {m n : ℕ} (tr : Trajectory m n) (x : Fin m → Fin n → ℝ) (t : ℕ) (j : Fin m) : ℝ :=
  tail (tr.lambda t j) (tr.rowX t j).val-pair (tr.lambda t j) (cdf (x j))

def residualY {m n : ℕ} (tr : Trajectory m n) (y : Fin m → Fin n → ℝ) (t : ℕ) (j : Fin m) : ℝ :=
  tail (tr.mu t j) (tr.rowY t j).val-pair (tr.mu t j) (cdf (y j))

noncomputable def averageCore {m n : ℕ} (tr : Trajectory m n) (v : Fin m → ℝ) (T : ℕ)
    (x y : Fin m → Fin n → ℝ) (testLambda testMu : Fin m → Fin (n+n) → ℝ) : ℝ :=
  ∑ j, v j*(codePayoff (meanP tr T j) (y j)-codePayoff (x j) (meanQ tr T j)+
    pair (testLambda j) (fun a => cdf (meanP tr T j) a-cdf (meanX tr T j) a)+
    pair (testMu j) (fun a => cdf (meanQ tr T j) a-cdf (meanY tr T j) a))

noncomputable def regretMean {m n : ℕ} (tr : Trajectory m n) (v : Fin m → ℝ) (T : ℕ)
    (x y : Fin m → Fin n → ℝ) (testLambda testMu : Fin m → Fin (n+n) → ℝ) : ℝ :=
  (∑ t ∈ Finset.range T, ∑ j, v j*fieldRegret (tr.p t j) (tr.q t j) (x j) (y j)
    (tr.lambda t j) (tr.mu t j) (testLambda j) (testMu j) (tr.rowX t j) (tr.rowY t j))/(T:ℝ)

theorem weighted_mean {m : ℕ} (v : Fin m → ℝ) (T : ℕ) (f : ℕ → Fin m → ℝ) :
    (∑ t ∈ Finset.range T, ∑ j, v j*f t j)/(T:ℝ)=∑ j, v j*((∑ t ∈ Finset.range T, f t j)/(T:ℝ)) := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_div,Finset.mul_sum,mul_div_assoc]

theorem core_mean {m n : ℕ} (tr : Trajectory m n) (T : ℕ) (x y : Fin m → Fin n → ℝ)
    (testLambda testMu : Fin m → Fin (n+n) → ℝ) (hy : ∀ j, ∑ a, y j a=1) (j : Fin m) :
    (∑ t ∈ Finset.range T, core tr x y testLambda testMu t j)/(T:ℝ)=
      codePayoff (meanP tr T j) (y j)-codePayoff (x j) (meanQ tr T j)+
        pair (testLambda j) (fun a => cdf (meanP tr T j) a-cdf (meanX tr T j) a)+
        pair (testMu j) (fun a => cdf (meanQ tr T j) a-cdf (meanY tr T j) a) := by
  have hx : (fun a => cdf (meanP tr T j) a-cdf (meanX tr T j) a)=
      mean T (fun t a => cdf (tr.p t j) a-rowCDF (tr.rowX t j) a) :=
    funext (cdf_difference_mean T (fun t => tr.p t j) (fun t => tr.rowX t j))
  have hq : (fun a => cdf (meanQ tr T j) a-cdf (meanY tr T j) a)=
      mean T (fun t a => cdf (tr.q t j) a-rowCDF (tr.rowY t j) a) :=
    funext (cdf_difference_mean T (fun t => tr.q t j) (fun t => tr.rowY t j))
  rw [hx,hq,pair_mean,pair_mean]
  unfold meanP meanQ
  rw [payoff_mean_left T _ _ (hy j),payoff_mean_right]
  simp only [core,Finset.sum_add_distrib,Finset.sum_sub_distrib,add_div,sub_div]

theorem average_cancellation {m n : ℕ} (tr : Trajectory m n) (v : Fin m → ℝ) (T : ℕ)
    (x y : Fin m → Fin n → ℝ) (testLambda testMu : Fin m → Fin (n+n) → ℝ)
    (hq : ∀ t<T, ∀ j, ∑ a, tr.q t j a=1) (hy : ∀ j, ∑ a, y j a=1) :
    regretMean tr v T x y testLambda testMu=averageCore tr v T x y testLambda testMu+
      (∑ t ∈ Finset.range T, ∑ j, v j*residualX tr x t j)/(T:ℝ)+
      (∑ t ∈ Finset.range T, ∑ j, v j*residualY tr y t j)/(T:ℝ) := by
  have hstep : (∑ t ∈ Finset.range T, ∑ j, v j*fieldRegret (tr.p t j) (tr.q t j) (x j) (y j)
      (tr.lambda t j) (tr.mu t j) (testLambda j) (testMu j) (tr.rowX t j) (tr.rowY t j))=
      ∑ t ∈ Finset.range T, ∑ j, v j*(core tr x y testLambda testMu t j+residualX tr x t j+residualY tr y t j) := by
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun value => v j*value) (GeneralPaperFourLossAlgebra.cancellation _ _ _ _ _ _ _ _ _ _ (hq t (Finset.mem_range.mp ht) j))
  unfold regretMean
  rw [hstep]
  simp only [mul_add,Finset.sum_add_distrib,add_div]
  congr 2
  rw [weighted_mean]
  unfold averageCore
  apply Finset.sum_congr rfl
  intro j hj
  rw [core_mean tr T x y testLambda testMu hy j]

theorem average_lower (T : ℕ) (hT : 0<T) (f : ℕ → ℝ) (lower : ℝ) (hf : ∀ t<T, lower≤f t) :
    lower≤(∑ t ∈ Finset.range T, f t)/(T:ℝ) := by
  have hs := Finset.sum_le_sum (s:=Finset.range T) (fun t ht => hf t (Finset.mem_range.mp ht))
  have hc : (∑ _t ∈ Finset.range T, lower)=(T:ℝ)*lower := by simp
  rw [hc] at hs
  apply (le_div_iff₀ (by exact_mod_cast hT : (0:ℝ)<T)).mpr
  nlinarith only [hs]

end Blotto.GeneralPaperFourAverageAlgebra
