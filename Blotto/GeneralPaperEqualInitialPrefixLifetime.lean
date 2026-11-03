import Blotto.GeneralPaperEqualDenominatorLifetime
import Blotto.GeneralPaperNativeScaleConstructionStorage

/-! Actual native positive rounding and complete length construction.
Original values/budget and the rounded return/work record remain owned at
entry, callback and return boundaries. Old checked scale/round/sum and array
observers are reused at the exact c=128 producer, without value reduction. -/
namespace Blotto.GeneralPaperEqualInitialPrefixLifetime
open GeneralPaperEncodedScalarStorage (natBits fields)
open GeneralPaperEncodedBasisStorage (arrayFootprint)
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

def raw {n : ℕ} (model : RationalCostModel) (W exponent : ℕ) (values : FixedArrayTable n ℚ) :=
  GeneralPaperValueRoundingPaperContract.run true model W 128 exponent values

def roundingTime {n : ℕ} (model : RationalCostModel) (W exponent : ℕ) (values : FixedArrayTable n ℚ) : ℕ :=
  GeneralPaperNativeScaleConstructionStorage.roundingPrice model W 128 n exponent (GeneralPaperValueRoundingInputPrice.inputSize values)

def inputOwner {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  arrayFootprint (GeneralPaperSummaryArrayExecution.arrayWord W n) rationalWordWidth values +
    arrayFootprint A rationalWordWidth values + rationalWordWidth budget +
    fields A [W, A, n, exponent, (raw model W exponent values).2] + 128 * A

def inputProfile {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  2 * GeneralPaperValueRoundingInputPrice.inputSize values + n * (GeneralPaperSummaryArrayExecution.arrayWord W n + A) +
    64 * GeneralPaperSummaryArrayExecution.arrayWord W n + 64 * A + rationalWordWidth budget +
    5 * (natBits (W + A + n + exponent + roundingTime model W exponent values + 1) + A) + 160 * A

theorem input_bound {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) :
    inputOwner model W A exponent values budget ≤ inputProfile model W A exponent values budget := by
  have hWork : (raw model W exponent values).2 ≤ roundingTime model W exponent values :=
    GeneralPaperNativeScaleConstructionStorage.rounding_work model W 128 exponent values v hv
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A
    (W + A + n + exponent + roundingTime model W exponent values + 1) [W, A, n, exponent, (raw model W exponent values).2] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 5 * (natBits (W + A + n + exponent + roundingTime model W exponent values + 1) + A) + 32 * A at hFields
  unfold inputOwner inputProfile
  rw [GeneralPaperEqualPrefixOwners.original_exact, GeneralPaperEqualPrefixOwners.original_exact]
  nlinarith only [hFields]

def roundedOwner {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  inputOwner model W A exponent values budget +
    GeneralPaperEqualPrefixOwners.roundedFoot (GeneralPaperSummaryArrayExecution.arrayWord W n)
      (raw model W exponent values).1.1 (raw model W exponent values).1.2 + natBits (raw model W exponent values).2 + 64 * A

def roundedProfile {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  inputProfile model W A exponent values budget +
    GeneralPaperEqualPrefixOwners.roundedProfile (GeneralPaperSummaryArrayExecution.arrayWord W n) n (binaryWordWidth n + exponent + 9) +
    natBits (roundingTime model W exponent values) + 64 * A

theorem rounded_bound {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) :
    roundedOwner model W A exponent values budget ≤ roundedProfile model W A exponent values budget := by
  have hInput := input_bound model W A exponent values v hv budget
  have hRaw := GeneralPaperEqualPrefixOwners.native_rounded true model W (GeneralPaperSummaryArrayExecution.arrayWord W n) exponent values v hv
  change GeneralPaperEqualPrefixOwners.roundedFoot (GeneralPaperSummaryArrayExecution.arrayWord W n)
    (raw model W exponent values).1.1 (raw model W exponent values).1.2 ≤ _ at hRaw
  have hWork := GeneralPaperNativeScaleConstructionStorage.rounding_work model W 128 exponent values v hv
  have hBits : natBits (raw model W exponent values).2 ≤ natBits (roundingTime model W exponent values) :=
    Nat.add_le_add_left (binaryWordWidth_mono hWork) 1
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hInput hRaw) hBits) _

inductive Phase (n : ℕ) where
  | rounding (cursor : ℕ) (h : cursor ≤ n)
  | rounded
  | conversion
  | length (i : Fin n)
  | returned

def window {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : Phase n → ℕ
  | .rounding cursor h => inputOwner model W A exponent values budget +
      GeneralPaperNativeScaleConstructionStorage.roundingWindow model W 128 exponent values cursor h
  | .rounded => roundedOwner model W A exponent values budget
  | .conversion => GeneralPaperEqualDenominatorLifetime.window A n (raw model W exponent values).1.2
      (roundedOwner model W A exponent values budget)
  | .length i => GeneralPaperEqualLengthPhaseStorage.phaseWindow model A (raw model W exponent values).1.1
      (raw model W exponent values).1.2 i.val i.isLt (roundedOwner model W A exponent values budget)
  | .returned => GeneralPaperEqualLengthReturnStorage.returnWindow model A (raw model W exponent values).1.1
      (raw model W exponent values).1.2 (roundedOwner model W A exponent values budget)

def profile {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  max (inputProfile model W A exponent values budget + GeneralPaperNativeScaleConstructionStorage.roundingProfile model W 128 n exponent
      (GeneralPaperValueRoundingInputPrice.inputSize values))
    (max (roundedProfile model W A exponent values budget)
      (max (GeneralPaperEqualDenominatorLifetime.profile A n (binaryWordWidth n + exponent + 11) (roundedProfile model W A exponent values budget))
        (max (GeneralPaperEqualLengthPhaseStorage.profile model A n (binaryWordWidth n + exponent + 11) (roundedProfile model W A exponent values budget))
          (GeneralPaperEqualLengthReturnStorage.profile model A n (binaryWordWidth n + exponent + 11) (roundedProfile model W A exponent values budget)))))

theorem length_borrowed_mono (model : RationalCostModel) (A n s B C : ℕ) (h : B ≤ C) :
    GeneralPaperEqualLengthPhaseStorage.profile model A n s B ≤ GeneralPaperEqualLengthPhaseStorage.profile model A n s C := by
  unfold GeneralPaperEqualLengthPhaseStorage.profile
  omega

theorem return_borrowed_mono (model : RationalCostModel) (A n s B C : ℕ) (h : B ≤ C) :
    GeneralPaperEqualLengthReturnStorage.profile model A n s B ≤ GeneralPaperEqualLengthReturnStorage.profile model A n s C := by
  unfold GeneralPaperEqualLengthReturnStorage.profile
  omega

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) (phase : Phase n) :
    window model W A exponent values budget phase ≤ profile model W A exponent values budget := by
  have hInput := input_bound model W A exponent values v hv budget
  have hRounded := rounded_bound model W A exponent values v hv budget
  cases phase with
  | rounding cursor h =>
    have hRound := GeneralPaperNativeScaleConstructionStorage.rounding_bounded model W 128 exponent values v hv cursor h
    exact (Nat.add_le_add hInput hRound).trans (le_max_left _ _)
  | rounded => exact hRounded.trans ((le_max_left _ _).trans (le_max_right _ _))
  | conversion =>
    have hD := GeneralPaperEqualNativeSampler.roundDen_word true model W exponent values v hv
    have hConvert := GeneralPaperEqualDenominatorLifetime.bounded A n (raw model W exponent values).1.2
      (binaryWordWidth n + exponent + 11) (roundedOwner model W A exponent values budget) (by omega) (hD.trans (by omega))
    have hBound := hConvert.trans (GeneralPaperEqualDenominatorLifetime.borrowed_mono A n _ _ _ hRounded)
    exact hBound.trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  | length i =>
    have hLength := GeneralPaperEqualLengthPhaseStorage.native true model W A exponent values v hv i.val i.isLt
      (roundedOwner model W A exponent values budget)
    have hBound := hLength.trans (length_borrowed_mono model A n _ _ _ hRounded)
    exact hBound.trans ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  | returned =>
    have hReturn := GeneralPaperEqualLengthReturnStorage.native true model W A exponent values v hv
      (roundedOwner model W A exponent values budget)
    have hBound := hReturn.trans (return_borrowed_mono model A n _ _ _ hRounded)
    exact hBound.trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))

theorem source_prices {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    let w := (GeneralPaperEqualAddressedPreparation.run true model W A exponent values v hv small budget).2.1.1
    (raw model W exponent values).2 = w.rounding ∧
      (GeneralPaperEqualLengthArray.run model A (raw model W exponent values).1.1 (raw model W exponent values).1.2).2 = w.lengths := by
  simp only [raw, GeneralPaperEqualAddressedPreparation.run]
  exact ⟨True.intro, True.intro⟩

end Blotto.GeneralPaperEqualInitialPrefixLifetime
