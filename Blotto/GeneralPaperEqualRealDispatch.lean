import Blotto.GeneralPaperEqualRealBranch

/-! Full equal-budget real preparation from original normalized rational
values. Round once, materialize lengths once, then execute exactly the
dominant or grouped branch selected by the stored-array scan. -/
namespace Blotto.GeneralPaperEqualRealDispatch
open GeneralPaperEqualNativeSampler (rounded)
open GeneralPaperEqualRealBranch (Prepared outputLaw)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def run {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) : Prepared (rounded false model 1 k values v hv) k budget × ℕ :=
  let raw := GeneralPaperValueRoundingPaperContract.run false model 1 128 k values
  let hp := GeneralPaperValueRoundingPaperContract.positivity false model 1 128 k (by decide) values v hv
  let r := GeneralPaperNativeRationalValues.selector raw.1.2 hp.1 raw.1.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum false model 1 128 k values)
  let lengths := GeneralPaperEqualRealPrefix.lengths raw.1.1 raw.1.2
  let hL : ∀ j, lengths.1.read j = 2 * r.weight j := by
    intro j
    rw [GeneralPaperEqualRealPrefix.lengths_data, FixedArrayTable.read_ofFn]
    rfl
  let actual := GeneralPaperEqualRealBranch.prepare r k budget lengths.1 hL
  (actual.1, raw.2 + lengths.2 + actual.2 + 128)

def bound (n k : ℕ) : ℕ :=
  GeneralPaperValueRoundingDriver.arithmeticProfile n (GeneralPaperValueRoundingPaperContract.scale 128 n k) +
    2048 * (n + 1) + 128 * (binaryWordWidth (k + 5) + 1) ^ 2 + 2150592

theorem work {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) :
    (run model k values v hv budget).2 ≤ bound n k := by
  let raw := GeneralPaperValueRoundingPaperContract.run false model 1 128 k values
  have hr := GeneralPaperValueRoundingPaperContract.arithmetic_work model 128 k values v hv
  have hl := GeneralPaperEqualRealPrefix.lengths_work raw.1.1 raw.1.2
  have hk := Nat.pow_le_pow_left (Nat.add_le_add_right (binaryWordWidth_mono (by omega : k ≤ k + 5)) 1) 2
  have ht : ∀ (lengths : FixedArrayTable n ℚ)
      (hL : ∀ j, lengths.read j = 2 * (rounded false model 1 k values v hv).weight j),
      (GeneralPaperEqualRealBranch.prepare (rounded false model 1 k values v hv) k budget lengths hL).2 ≤
        1024 * (n + 1) + 64 * (binaryWordWidth (k + 5) + 1) ^ 2 + 2150064 :=
    fun lengths hL => GeneralPaperEqualRealBranch.prepare_work _ k budget lengths hL
  have ht' := ht (GeneralPaperEqualRealPrefix.lengths raw.1.1 raw.1.2).1 (by
    intro j; rw [GeneralPaperEqualRealPrefix.lengths_data, FixedArrayTable.read_ofFn]; rfl)
  unfold run bound
  dsimp only
  change raw.2 + (GeneralPaperEqualRealPrefix.lengths raw.1.1 raw.1.2).2 +
    (GeneralPaperEqualRealBranch.prepare (rounded false model 1 k values v hv) k budget
      (GeneralPaperEqualRealPrefix.lengths raw.1.1 raw.1.2).1 _).2 + 128 ≤ _
  change raw.2 ≤ _ at hr
  omega

theorem bound_rate (n k : ℕ) : bound n k ≤
    8388608 * (n + 1) * (GeneralPaperEqualRealPreparationRates.logarithm n k) ^ 2 := by
  have h := GeneralPaperEqualRealPreparationRates.bound n k
  let L := GeneralPaperEqualRealPreparationRates.logarithm n k
  have hL : 1 ≤ L := by dsimp [L, GeneralPaperEqualRealPreparationRates.logarithm]; omega
  have hn : n + 1 ≤ (n + 1) * L ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have hp : 1 ≤ (n + 1) * L ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have he : bound n k = GeneralPaperEqualRealPreparation.bound n k + 1024 * (n + 1) + 64 := by
    unfold bound GeneralPaperEqualRealPreparation.bound
    omega
  rw [he]
  change _ ≤ 8388608 * (n + 1) * L ^ 2
  change GeneralPaperEqualRealPreparation.bound n k ≤ 4194304 * (n + 1) * L ^ 2 at h
  nlinarith only [h, hn, hp]

theorem original_regret {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (hB : 0 < budget) :
    let p := (run model k values v hv budget).1
    Supported (budget : ℝ) (outputLaw p) ∧
      regret v.values (budget : ℝ) (outputLaw p) (outputLaw p) ≤ 3 * (1 / (2 : ℝ) ^ k) / 32 := by
  let p := (run model k values v hv budget).1
  have h := GeneralPaperEqualRealBranch.rounded_regret p hB
  have hd := GeneralPaperEqualRoundedBoundary.distance false model 1 k values v hv
  change GeneralPaperValuePerturbation.distance v.values (rounded false model 1 k values v hv).values ≤ _ at hd
  have hBr : (0 : ℝ) ≤ budget := by exact_mod_cast hB.le
  have ht := GeneralPaperValuePerturbation.regret_le_shift v.values (rounded false model 1 k values v hv).values
    (budget : ℝ) hBr (outputLaw p) (outputLaw p)
  change Supported (budget : ℝ) (outputLaw p) ∧
    regret v.values (budget : ℝ) (outputLaw p) (outputLaw p) ≤ 3 * (1 / (2 : ℝ) ^ k) / 32
  have hPos : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ k := by positivity
  exact ⟨h.1, by linarith only [h.2, hd, ht, hPos]⟩

def accuracy {n : ℕ} (model : RationalCostModel) (eps : ℚ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) :=
  let selected := GeneralPaperDyadicAccuracy.prepare eps
  let actual := run model selected.exponent values v hv budget
  (actual.1, selected.work + actual.2 + 64)

theorem epsilon {n : ℕ} (model : RationalCostModel) (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (hB : 0 < budget) :
    let p := (accuracy model eps values v hv budget).1
    Supported (budget : ℝ) (outputLaw p) ∧ regret v.values (budget : ℝ) (outputLaw p) (outputLaw p) ≤ (eps : ℝ) := by
  have h := original_regret model (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv budget hB
  have he := (GeneralPaperDyadicAccuracy.accuracy_bounds eps hp hOne).2
  rw [GeneralPaperDyadicAccuracy.accuracy_power] at he
  have he' : (1 / (2 : ℝ) ^ (GeneralPaperDyadicAccuracy.prepare eps).exponent) ≤ (eps : ℝ) := by
    have hc : (((1 / (2 : ℚ) ^ (GeneralPaperDyadicAccuracy.prepare eps).exponent : ℚ) : ℝ)) ≤ (eps : ℝ) := by exact_mod_cast he
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hc
  have hp' : (0 : ℝ) < eps := by exact_mod_cast hp
  dsimp only [accuracy]
  dsimp only at h
  exact ⟨h.1, by linarith only [h.2, he', hp']⟩

theorem accuracy_work {n : ℕ} (model : RationalCostModel) (eps : ℚ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) :
    (accuracy model eps values v hv budget).2 ≤
      16777216 * (n + 1) * (binaryWordWidth n + binaryWordWidth ⌈eps⁻¹⌉₊ + 16) ^ 2 := by
  have h := (work model (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv budget).trans
    (bound_rate n (GeneralPaperDyadicAccuracy.prepare eps).exponent)
  have ha := GeneralPaperDyadicAccuracy.prepare_work eps
  have he := GeneralPaperDyadicAccuracy.prepare_work_exact eps
  have hk : (GeneralPaperDyadicAccuracy.prepare eps).exponent ≤ binaryWordWidth ⌈eps⁻¹⌉₊ := by omega
  let L := binaryWordWidth n + binaryWordWidth ⌈eps⁻¹⌉₊ + 16
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hWord : binaryWordWidth ⌈eps⁻¹⌉₊ ≤ L := by dsimp [L]; omega
  have hCompare : GeneralPaperEqualRealPreparationRates.logarithm n (GeneralPaperDyadicAccuracy.prepare eps).exponent ≤ L := by
    unfold GeneralPaperEqualRealPreparationRates.logarithm; dsimp [L]; omega
  have hScale := Nat.mul_le_mul_left (8388608 * (n + 1)) (Nat.pow_le_pow_left hCompare 2)
  have hS : L ≤ (n + 1) * L ^ 2 := by
    have h1 : L ≤ L ^ 2 := by nlinarith only [hL]
    exact h1.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hOne : 1 ≤ (n + 1) * L ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  dsimp only [accuracy]
  change _ ≤ 16777216 * (n + 1) * L ^ 2
  nlinarith only [h, ha, hWord, hScale, hS, hOne]

end Blotto.GeneralPaperEqualRealDispatch
