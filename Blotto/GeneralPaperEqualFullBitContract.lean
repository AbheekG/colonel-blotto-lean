import Blotto.GeneralPaperEqualStoredBitSampler

/-! Native complete bit-draw headlines for the same returned sampler. Its
address is prepared from the retained budget's actual word length. Original
input length/accuracy calibration are analysis bounds, never draw arguments. -/
namespace Blotto.GeneralPaperEqualFullBitContract
open MeasureTheory
open scoped BigOperators Classical ENNReal
open GeneralPaperEqualRejectionTraceMeasure
open GeneralPaperEqualStoredBitSampler (native observed)
open GeneralPaperEqualNativeSampler (rounded segmentHeight)
open GeneralPaperEqualBitDrawRates (word log size address)
set_option autoImplicit false
set_option maxHeartbeats 1000000

def bound (model : RationalCostModel) (n k b : ℕ) : ℕ :=
  8589934592 * (n + 1) * model.rat (word n k b) * log n k b

theorem controller_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let p := GeneralPaperEqualNativeCache.prepare bits model W k values v hv small budget
    2 * (GeneralPaperEqualBooleanTrial.bound p + 8) ≤ 4294967296 * (binaryWordWidth n + k + 10) := by
  dsimp only
  have h := GeneralPaperEqualBooleanCategoricalContract.small_bound
    (GeneralPaperEqualNativeCache.prepare bits model W k values v hv small budget)
    (GeneralPaperEqualNativeCache.compact_count _ small).2
  have hw := GeneralPaperEqualNativeCache.rangeBits bits model W k values v hv small budget
  omega

theorem native_total_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) (b : ℕ) :
    let p := GeneralPaperEqualNativeCache.prepare bits model W k values v hv small budget
    let m := (GeneralPaperEqualFiniteKernel.terminal (rounded bits model W k values v hv) small).groups.length
    2 * (GeneralPaperEqualBooleanTrial.bound p + 8) +
      GeneralPaperEqualBitPostprocessing.bound model (address n m k b) n m (k + 5) (segmentHeight n k) b
        (binaryWordWidth n + k + 9) + 16 * address n m k b + 16 ≤ bound model n k b := by
  dsimp only
  have hc := controller_bound bits model W k values v hv small budget
  have hp := GeneralPaperEqualBitDrawRates.post_bound model n _ k b (GeneralPaperEqualNativeCache.group_count _ small)
  let R := model.rat (word n k b)
  let L := log n k b
  have hL : 1 ≤ L := by dsimp [L, log]; omega
  have hX : binaryWordWidth n + k + 10 ≤ R := by
    have hs : binaryWordWidth n + k + 10 ≤ size n k b := by unfold size; omega
    have hw : size n k b ≤ word n k b := by unfold word; omega
    exact (hs.trans hw).trans (model.word_le _)
  have hn := Nat.mul_le_mul (show 1 ≤ n + 1 by omega) hX
  simp only [Nat.one_mul] at hn
  have hLast := Nat.mul_le_mul_left ((n + 1) * R) hL
  simp only [Nat.mul_one] at hLast
  have hPay := Nat.mul_le_mul_left 4294967296 (hn.trans hLast)
  unfold bound
  change _ ≤ 8589934592 * (n + 1) * R * L
  nlinarith only [hc, hp, hPay]

theorem native_expected_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let sampler := native bits model W k values v hv small budget
    (∫⁻ trace, ((observed sampler model trace).work : ℝ≥0∞)
      ∂(law sampler.prepared.D sampler.prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) : Measure (Trace sampler.prepared.D sampler.prepared.midpointBits))) ≤
      (bound model n k (rationalWordWidth budget) : ℝ≥0∞) := by
  dsimp only
  let sampler := native bits model W k values v hv small budget
  have hs : 2 ≤ segmentHeight n k := by
    unfold segmentHeight GeneralPaperEqualNativeSampler.fieldHeight expressionHeightBudget
    omega
  have he := GeneralPaperEqualFullBitDraw.expected_work sampler.categorical model sampler.address hs
    (GeneralPaperEqualNativeSampler.native_lottery_height bits model W k values v hv small)
    (rationalHeight_of_wordWidth budget)
    (by omega : 2 ≤ binaryWordWidth n + k + 9)
    (GeneralPaperEqualNativeCache.route_height bits model W k values v hv small budget)
  apply he.trans
  have hNat := native_total_bound bits model W k values v hv small budget (rationalWordWidth budget)
  exact_mod_cast hNat

theorem bound_mono (model : RationalCostModel) (n : ℕ) {k K b B : ℕ} (hk : k ≤ K) (hb : b ≤ B) :
    bound model n k b ≤ bound model n K B := by
  have hw : word n k b ≤ word n K B := by unfold word size; omega
  have hl : log n k b ≤ log n K B :=
    Nat.add_le_add_right (binaryWordWidth_mono (by omega : n + word n k b + 32 ≤ n + word n K B + 32)) 1
  exact Nat.mul_le_mul (Nat.mul_le_mul_left (8589934592 * (n + 1)) (model.monotone hw)) hl

theorem fast_bound {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (n k b : ℕ) : bound model n k b ≤
      8589934592 * C * (n + 1) * word n k b * (log n k b) ^ (d + 1) := by
  have hl : GeneralPaperFastRationalModel.logFactor d (word n k b) ≤ (log n k b) ^ d := by
    unfold GeneralPaperFastRationalModel.logFactor log
    exact Nat.pow_le_pow_left (Nat.add_le_add_right (binaryWordWidth_mono (by omega : word n k b + 1 ≤ n + word n k b + 32)) 1) d
  have hp := (hg (word n k b)).trans (Nat.mul_le_mul_left (C * word n k b) hl)
  calc
    _ ≤ 8589934592 * (n + 1) * (C * word n k b * (log n k b) ^ d) * log n k b :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp)
    _ = _ := by rw [pow_succ]; ring

theorem accuracy_expected_work {n L0 : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ) (small : ∀ j, 2 * (rounded bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1)
    (budget : ℚ) (hB : RationalHeight budget L0) :
    let sampler := native bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget
    (∫⁻ trace, ((observed sampler model trace).work : ℝ≥0∞)
      ∂(law sampler.prepared.D sampler.prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) : Measure (Trace sampler.prepared.D sampler.prepared.midpointBits))) ≤
      (bound model n (binaryWordWidth ⌈eps⁻¹⌉₊) (1 + 2 * L0) : ℝ≥0∞) := by
  dsimp only
  have hk : (GeneralPaperDyadicAccuracy.prepare eps).exponent ≤ binaryWordWidth ⌈eps⁻¹⌉₊ := by
    have h0 := GeneralPaperDyadicAccuracy.prepare_work eps
    have h1 := GeneralPaperDyadicAccuracy.prepare_work_exact eps
    omega
  apply (native_expected_work bits model W _ values v hv small budget).trans
  have hh := bound_mono model n hk (rationalWordWidth_of_height hB)
  exact_mod_cast hh

def paperBound (C d n k b : ℕ) : ℕ :=
  17179869184 * C * n * word n k b * (log n k b) ^ (d + 1)

theorem fast_bound_fields {model : RationalCostModel} {C d n : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (v : RationalFieldSelector n) (k b : ℕ) :
    bound model n k b ≤ paperBound C d n k b := by
  have hn : n + 1 ≤ 2 * n := by have h := v.fields_positive; omega
  calc
    _ ≤ 8589934592 * C * (n + 1) * word n k b * (log n k b) ^ (d + 1) := fast_bound hg n k b
    _ ≤ 8589934592 * C * (2 * n) * word n k b * (log n k b) ^ (d + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn))
    _ = _ := by unfold paperBound; ring

theorem accuracy_fast_expected_work {n L0 C d : ℕ} (bits : Bool) (model : RationalCostModel)
    (hg : GeneralPaperFastRationalModel.Growth model C d) (W : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ) (small : ∀ j, 2 * (rounded bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1)
    (budget : ℚ) (hB : RationalHeight budget L0) :
    let sampler := native bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget
    (∫⁻ trace, ((observed sampler model trace).work : ℝ≥0∞)
      ∂(law sampler.prepared.D sampler.prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) : Measure (Trace sampler.prepared.D sampler.prepared.midpointBits))) ≤
      (paperBound C d n (binaryWordWidth ⌈eps⁻¹⌉₊) (1 + 2 * L0) : ℝ≥0∞) := by
  dsimp only
  apply (accuracy_expected_work bits model W values v hv eps small budget hB).trans
  have hh := fast_bound_fields hg v (binaryWordWidth ⌈eps⁻¹⌉₊) (1 + 2 * L0)
  exact_mod_cast hh

end Blotto.GeneralPaperEqualFullBitContract
