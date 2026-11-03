import Blotto.GeneralPaperUniformListSampler

/-! Sharp uniform-list length and logarithmic randomness on native
controls, before the actual-return joins for both computational models. -/
namespace Blotto.GeneralPaperUniformListCounts
open GeneralPaperStoredStrategySampler (Sampler)
open GeneralPaperUniformListSampler
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem native_length {n T K m k : ℕ} (sampler : Sampler n T K)
    (epsilon : ℚ) (hE : 0 < epsilon) (hOne : epsilon < 1) (hn : 0 < n)
    (hm : m ≤ n) (hM : (m : ℚ) ≤ 36*GeneralPaperRealHeadlineParameters.nStar n epsilon)
    (hPower : (2 : ℚ)^k ≤ 2/epsilon)
    (hRows : sampler.controls.rows =
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows)
    (hShifts : sampler.controls.shifts = GeneralPaperNativeSelectedSecurity.count k) :
    (length sampler : ℚ) ≤ ((2^78*37 : ℕ) : ℚ) *
      GeneralPaperRealHeadlineParameters.nStar n epsilon / epsilon^4 * (binaryWordWidth (n+4) : ℚ) := by
  let N := GeneralPaperRealHeadlineParameters.nStar n epsilon
  have hN : 1 ≤ N := GeneralPaperRealHeadlineParameters.nstar_positive n hn epsilon hE hOne
  have hmN : (m : ℚ)+1 ≤ 37*N := by linarith only [hM, hN]
  have hS : GeneralPaperNativeSelectedSecurity.count k = 64*2^k := by
    rw [GeneralPaperNativeSelectedSecurity.count_power]
    norm_num [pow_add]
    ring
  have hLen : length sampler ≤
      2^74*(m+1)*(2^k)^4*binaryWordWidth (m+3) := by
    rw [length_product]
    calc
      _ ≤ sampler.controls.rows * sampler.controls.shifts :=
        Nat.mul_le_mul_left _ (GeneralPaperExactStoredSampler.shift_count_le sampler)
      _ ≤ (2^68*(m+1)*(2^k)^3*binaryWordWidth (m+3))*(64*2^k) := by
        rw [hRows, hShifts, hS]
        exact Nat.mul_le_mul_right _ (GeneralPaperDescriptionSourceParameters.rows m k)
      _ = _ := by ring
  have hLenQ : (length sampler : ℚ) ≤
      (2 : ℚ)^74*((m : ℚ)+1)*((2 : ℚ)^k)^4*(binaryWordWidth (m+3) : ℚ) := by
    exact_mod_cast hLen
  have hW := binaryWordWidth_mono (show m+3 ≤ n+4 by omega)
  calc
    _ ≤ (2 : ℚ)^74*((m : ℚ)+1)*((2 : ℚ)^k)^4*(binaryWordWidth (m+3) : ℚ) := hLenQ
    _ ≤ (2 : ℚ)^74*(37*N)*(2/epsilon)^4*(binaryWordWidth (n+4) : ℚ) := by gcongr
    _ = _ := by dsimp only [N]; push_cast; ring

theorem at_word_headlines (model : RationalCostModel) (W : ℕ)
    (p : GeneralPaperNativeResourceDomain.Problem)
    (hOne : GeneralPaperNativeWorkingSpaceHeadline.epsilon p < 1) :
    let actual := GeneralPaperArbitraryPreparationDraw.returned model W p
    let o := actual.raw.strategies.original.reduced
    let k := actual.raw.exponent
    let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    ∀ sampler : Sampler p.n t.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      actual.sampler = some sampler →
      (length sampler : ℚ) ≤ ((2^78*37 : ℕ) : ℚ) *
        GeneralPaperRealHeadlineParameters.nStar p.n (GeneralPaperNativeWorkingSpaceHeadline.epsilon p) /
          (GeneralPaperNativeWorkingSpaceHeadline.epsilon p)^4 * (binaryWordWidth (p.n+4) : ℚ) ∧
      Nat.log2 (length sampler) ≤ 4*binaryWordWidth ⌈(GeneralPaperNativeWorkingSpaceHeadline.epsilon p)⁻¹⌉₊ +
        2*binaryWordWidth (p.n+4) + 87 := by
  dsimp only
  intro sampler hSampler
  have hc := GeneralPaperExactSamplerCounts.native_controls model W W W
    p.words p.values p.selector p.correct p.budget p.budget_valid sampler hSampler
  have hr := GeneralPaperArbitraryPreparationDraw.returned_reduced model W p
  have hk := GeneralPaperArbitraryPreparationDraw.returned_exponent model W p
  dsimp only [GeneralPaperArbitraryPreparationDraw.returned] at hr hk
  have hm : (GeneralPaperNativeResourceParameters.reduced model p).m ≤ p.n :=
    (GeneralPaperOriginalValueReduction.count_bounds false model 1
      (GeneralPaperNativeResourceDomain.exponent p) p.values p.selector p.correct).2.1
  have hcBits := hc.2.1.trans (congrArg₂
    (fun (o : GeneralPaperReducedValuesDriver.Output p.n) (k : ℕ) =>
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rowBits) hr hk)
  have hcShifts := hc.2.2.2.1.trans (congrArg GeneralPaperNativeSelectedSecurity.count hk)
  have hCount := GeneralPaperExactSamplerCounts.at_word_counts model W p hOne sampler hSampler
  have hLength : (length sampler : ℚ) =
      (sampler.controls.rows : ℚ)*(GeneralPaperExactStoredSampler.shifts sampler : ℚ) := by
    exact_mod_cast length_product sampler
  have hSize : (length sampler : ℚ) ≤ ((2^78*37 : ℕ) : ℚ) *
      GeneralPaperRealHeadlineParameters.nStar p.n (GeneralPaperNativeWorkingSpaceHeadline.epsilon p) /
        (GeneralPaperNativeWorkingSpaceHeadline.epsilon p)^4 * (binaryWordWidth (p.n+4) : ℚ) := by
    rw [hLength]
    calc
      _ ≤ (((2^68*296 : ℕ) : ℚ)*
        GeneralPaperRealHeadlineParameters.nStar p.n (GeneralPaperNativeWorkingSpaceHeadline.epsilon p) /
        (GeneralPaperNativeWorkingSpaceHeadline.epsilon p)^3 * (binaryWordWidth (p.n+4) : ℚ)) *
          (128/GeneralPaperNativeWorkingSpaceHeadline.epsilon p) := by
        exact mul_le_mul hCount.1 hCount.2.1 (Nat.cast_nonneg _)
          ((Nat.cast_nonneg sampler.controls.rows).trans hCount.1)
      _ = _ := by push_cast; ring
  have hBits := random_bits_bound sampler hm hcBits hcShifts
  have hExponent := GeneralPaperRealHeadlineParameters.exponent_bound
    (GeneralPaperNativeWorkingSpaceHeadline.epsilon p)
  rw [← GeneralPaperNativeWorkingSpaceHeadline.exponent_exact p] at hExponent
  exact ⟨hSize, hBits.trans (by omega)⟩

end Blotto.GeneralPaperUniformListCounts
