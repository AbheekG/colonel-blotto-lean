import Blotto.GeneralPaperEqualRealCacheDraw

/-! The smaller-cache real producer has a quasilinear field bound using
only n and constructed accuracy. Original rational precision and binary
accuracy encoding length do not enter the executed real-model prices. -/
namespace Blotto.GeneralPaperEqualRealPreparationRates
open GeneralPaperEqualNativeSampler (rounded)
set_option autoImplicit false
set_option maxHeartbeats 1800000

def logarithm (n k : ℕ) : ℕ := binaryWordWidth n + k + 16

theorem bound (n k : ℕ) : GeneralPaperEqualRealPreparation.bound n k ≤
    4194304 * (n + 1) * (logarithm n k) ^ 2 := by
  let L := logarithm n k
  have hL : 1 ≤ L := by dsimp [L, logarithm]; omega
  have h128 : binaryWordWidth 128 = 8 := by decide
  have hPow : binaryWordWidth (2 ^ k) = k + 1 := by simp only [binaryWordWidth, Nat.log2_two_pow]
  have h0 := binaryWordWidth_mul (128 * n) (2 ^ k)
  have h1 := binaryWordWidth_mul 128 n
  rw [h128] at h1
  rw [hPow] at h0
  have hScale : binaryWordWidth (GeneralPaperValueRoundingPaperContract.scale 128 n k) ≤ L := by
    dsimp only [GeneralPaperValueRoundingPaperContract.scale, L, logarithm]
    omega
  have hWord := GeneralPaperEqualDrawAddressCapacity.word_le (k + 5)
  have hK : binaryWordWidth (k + 5) + 1 ≤ L := by dsimp [L, logarithm]; omega
  have hSquare := Nat.pow_le_pow_left hK 2
  have hQL : L ≤ L ^ 2 := by nlinarith only [hL]
  have hN := Nat.mul_le_mul_left n hScale
  have hNL := Nat.mul_le_mul_left n hQL
  have hNOne : n ≤ n * L ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have hS : L ^ 2 ≤ (n + 1) * L ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
  have hOne : 1 ≤ (n + 1) * L ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold GeneralPaperEqualRealPreparation.bound GeneralPaperValueRoundingDriver.arithmeticProfile
    GeneralPaperValueRoundArray.arithmeticProfile
  change _ ≤ 4194304 * (n + 1) * L ^ 2
  nlinarith only [hN, hNL, hNOne, hS, hOne, hSquare]

theorem preparation_work {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded false model 1 k values v hv).weight j ≤ 1) (budget : ℚ) :
    (GeneralPaperEqualRealPreparation.run model k values v hv small budget).2 ≤
      4194304 * (n + 1) * (logarithm n k) ^ 2 :=
  (GeneralPaperEqualRealPreparation.work model k values v hv small budget).trans (bound n k)

def run {n : ℕ} (model : RationalCostModel) (eps : ℚ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded false model 1 (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1)
    (budget : ℚ) :=
  let accuracy := GeneralPaperDyadicAccuracy.prepare eps
  let actual := GeneralPaperEqualRealPreparation.run model accuracy.exponent values v hv small budget
  (actual.1, accuracy.work + actual.2 + 64)

theorem work {n : ℕ} (model : RationalCostModel) (eps : ℚ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded false model 1 (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1)
    (budget : ℚ) : (run model eps values v hv small budget).2 ≤
      8388608 * (n + 1) * (binaryWordWidth n + binaryWordWidth ⌈eps⁻¹⌉₊ + 16) ^ 2 := by
  have h := preparation_work model (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget
  have ha := GeneralPaperDyadicAccuracy.prepare_work eps
  have he := GeneralPaperDyadicAccuracy.prepare_work_exact eps
  have hk : (GeneralPaperDyadicAccuracy.prepare eps).exponent ≤ binaryWordWidth ⌈eps⁻¹⌉₊ := by omega
  let L := binaryWordWidth n + binaryWordWidth ⌈eps⁻¹⌉₊ + 16
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hWord : binaryWordWidth ⌈eps⁻¹⌉₊ ≤ L := by dsimp [L]; omega
  have hCompare : logarithm n (GeneralPaperDyadicAccuracy.prepare eps).exponent ≤ L := by unfold logarithm; dsimp [L]; omega
  have hQ := Nat.pow_le_pow_left hCompare 2
  have hScale := Nat.mul_le_mul_left (4194304 * (n + 1)) hQ
  have hS : L ≤ (n + 1) * L ^ 2 := by
    have h1 : L ≤ L ^ 2 := by nlinarith only [hL]
    exact h1.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hOne : 1 ≤ (n + 1) * L ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  dsimp only [run]
  change _ ≤ 8388608 * (n + 1) * L ^ 2
  nlinarith only [h, ha, hWord, hScale, hS, hOne]

end Blotto.GeneralPaperEqualRealPreparationRates
