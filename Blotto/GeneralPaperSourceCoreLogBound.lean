import Blotto.GeneralPaperSharpDPArithmeticRate

/-! Remove unused original-ratio encoding heights from source arithmetic
bounds. The source price and rate must be proved invariant under this
analysis-only record map. No native input, budget or execution is changed. -/
namespace Blotto.GeneralPaperSourceCoreLogBound
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds
open GeneralPaperSourceRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1200000

def coreLog (x : Input) : ℕ := GeneralPaperSourcePreparationSizes.measure x.m (alphabet x).lambda x.k x.Qv

def analysisInput (x : Input) : Input where
  m := x.m
  k := x.k
  Qv := x.Qv
  B := 2
  b := 1/2
  hb := by norm_num
  hB := by norm_num [RationalHeight]
  reciprocal := x.reciprocal
  weights := x.weights
  weight_sum := x.weight_sum

theorem core_log_positive (x : Input) : 1≤coreLog x := by
  unfold coreLog GeneralPaperSourcePreparationSizes.measure
  omega

theorem mapped_log_bound (x : Input) : logSize (analysisInput x)≤2*coreLog x := by
  change 128+x.k+binaryWordWidth (x.m+1)+binaryWordWidth ((alphabet x).lambda+1)+binaryWordWidth (x.Qv+1)+
    binaryWordWidth (2+1)≤2*coreLog x
  rw [show binaryWordWidth (2+1)=2 by decide]
  unfold coreLog GeneralPaperSourcePreparationSizes.measure
  omega

theorem remove_unused_height {rate f : Input → ℕ} (hf : Soft rate f)
    (hprice : ∀ x,f (analysisInput x)=f x) (hrate : ∀ x,rate (analysisInput x)=rate x) :
    ∃ A e : ℕ,∀ x,f x≤A*rate x*(coreLog x)^e := by
  rcases hf with ⟨A,e,hA⟩
  refine ⟨A*2^e,e,?_⟩
  intro x
  have h := hA (analysisInput x)
  rw [hprice,hrate] at h
  apply h.trans
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (mapped_log_bound x) e)).trans_eq (by rw [mul_pow]; ring)

@[fun_prop]
theorem measure_square : Rated (fun x => (GeneralPaperSourcePreparationSizes.measure x.m (alphabet x).lambda x.k x.Qv+1)^2) 0 0 0 := by
  apply poly
  have hm := poly_tight _ measure_tight
  fun_prop

@[fun_prop]
theorem height_square : Rated (fun x => ((GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).height+1)^2) 0 0 0 := by
  apply poly
  have hh := poly_tight _ GeneralPaperNativeSourceWordGrowth.profit_height_tight
  fun_prop

@[fun_prop]
theorem rank_square : Rated (fun x => (35+x.k+1)^2) 0 0 0 := by
  apply poly
  have hk := poly_tight _ k_tight
  fun_prop

end Blotto.GeneralPaperSourceCoreLogBound
