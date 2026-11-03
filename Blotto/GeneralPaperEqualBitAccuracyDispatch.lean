import Blotto.GeneralPaperEqualBitDispatch

/-! The actual binary accuracy reader feeds its returned exponent directly
to dominant/grouped bit preparation. The wrapped return retains that exponent
and the selected sampler, with all accuracy and source work accounted for.
Global reference calibration and raw game parsing remain caller joins. -/
namespace Blotto.GeneralPaperEqualBitAccuracyDispatch
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2000000

def epsilon (words : BinaryAccuracyWords) : ℚ := (words.numerator.value : ℚ) / words.denominator.value

theorem epsilon_positive (words : BinaryAccuracyWords) : 0 < epsilon words :=
  div_pos (by exact_mod_cast words.numerator.value_pos) (by exact_mod_cast words.denominator.value_pos)

structure Prepared {n : ℕ} (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) where
  exponent : ℕ
  branch : GeneralPaperEqualBitBranch.Prepared
    (GeneralPaperEqualNativeSampler.rounded true model W exponent values v hv) exponent budget

noncomputable def outputLaw {n : ℕ} {model : RationalCostModel} {W : ℕ} {values : FixedArrayTable n ℚ}
    {v : RationalFieldSelector n} {hv : ∀ j, values.read j = v.weight j} {budget : ℚ}
    (p : Prepared model W values v hv budget) : Mixed n := GeneralPaperEqualBitBranch.outputLaw model p.branch

def run {n : ℕ} (model : RationalCostModel) (W A : ℕ) (words : BinaryAccuracyWords)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) :
    Prepared model W values v hv budget × ℕ :=
  let parsed := GeneralPaperBinaryAccuracy.prepare id A words
  let actual := GeneralPaperEqualBitDispatch.run model W A parsed.1 values v hv budget
  (⟨parsed.1, actual.1⟩, parsed.2 + actual.2 + 128 * A + 128)

theorem exponent_data {n : ℕ} (model : RationalCostModel) (W A : ℕ) (words : BinaryAccuracyWords)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) :
    (run model W A words values v hv budget).1.exponent = (GeneralPaperDyadicAccuracy.prepare (epsilon words)).exponent :=
  GeneralPaperBinaryAccuracy.exact_exponent id A words (epsilon words) rfl

theorem work {n : ℕ} (model : RationalCostModel) (W A : ℕ) (words : BinaryAccuracyWords)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) :
    (run model W A words values v hv budget).2 ≤
      GeneralPaperBinaryAccuracyConstructionStorage.price A (GeneralPaperBinaryAccuracyConstructionStorage.inputSize words) +
      GeneralPaperEqualBitDispatch.bound model W A (GeneralPaperBinaryAccuracy.prepare id A words).1 values budget + 128 * A + 128 := by
  have ha := GeneralPaperBinaryAccuracyConstructionStorage.work A words
  have hs := GeneralPaperEqualBitDispatch.work model W A (GeneralPaperBinaryAccuracy.prepare id A words).1 values v hv budget
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add ha hs) (128 * A)) 128

theorem equilibrium {n : ℕ} (model : RationalCostModel) (W A : ℕ) (words : BinaryAccuracyWords)
    (hOne : epsilon words < 1) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) (hB : 0 < budget) :
    let p := (run model W A words values v hv budget).1
    Supported (budget : ℝ) (outputLaw p) ∧
      regret v.values (budget : ℝ) (outputLaw p) (outputLaw p) ≤ (epsilon words : ℝ) := by
  dsimp only [run, outputLaw]
  rw [GeneralPaperBinaryAccuracy.exact_exponent id A words (epsilon words) rfl]
  exact GeneralPaperEqualBitDispatch.epsilon model W A values v hv (epsilon words) (epsilon_positive words) hOne budget hB

end Blotto.GeneralPaperEqualBitAccuracyDispatch
