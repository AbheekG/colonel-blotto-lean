import Blotto.GeneralPaperEqualPowerWidthLifetime

/-! Native midpoint-power/width construction retains the actual returned
categorical integer data and all earlier caller owners. Denominator width
comes from compact rational heights, without a supplied precision bound. -/
namespace Blotto.GeneralPaperEqualPowerWidthCaller
open GeneralPaperEqualNativeSampler (rounded segmentHeight)
open GeneralPaperEqualFiniteKernel (lottery)
open GeneralPaperPositiveSegmentCompaction (count)
open GeneralPaperEqualIntegerCallerLifetime (actual compacted)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem integer_denominator_word {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) (h : ∀ i, RationalHeight (p.weights.read i) s) :
    binaryWordWidth (GeneralPaperStoredCategoricalCounts.run p model A).1.D ≤ s * r + 1 := by
  have hD := GeneralPaperCategoricalIntegerLifetime.denominator_word p model A h
  change 1 + binaryWordWidth (GeneralPaperStoredCategoricalCounts.run p model A).1.D ≤ s * r + 2 at hD
  omega

def borrowed {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  GeneralPaperEqualIntegerCallerLifetime.window bits model W A exponent values v hv small budget .returned

def window {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperEqualPowerWidthLifetime.Phase (exponent + 5)) : ℕ :=
  GeneralPaperEqualPowerWidthLifetime.window model A (actual bits model W A exponent values v hv small budget).1.D
    (exponent + 5) (borrowed bits model W A exponent values v hv small budget) phase

def profile {n : ℕ} (model : RationalCostModel) (W A exponent c : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperEqualPowerWidthLifetime.profile model A (segmentHeight n exponent * c + 1) (exponent + 5)
    (GeneralPaperEqualIntegerCallerLifetime.profile model W A exponent values budget c)

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperEqualPowerWidthLifetime.Phase (exponent + 5)) :
    window true model W A exponent values v hv small budget phase ≤
      profile model W A exponent (count (lottery (rounded true model W exponent values v hv) small)) values budget := by
  let p := (compacted true model W A exponent values v hv small budget).1
  have hHeight := GeneralPaperPositiveSegmentCompaction.compact_height
    (lottery (rounded true model W exponent values v hv) small)
    (GeneralPaperEqualNativeSampler.native_lottery_height true model W exponent values v hv small)
  have hD := integer_denominator_word p model A (by intro i; rw [p.weight_correct]; exact hHeight.1 i)
  change binaryWordWidth (actual true model W A exponent values v hv small budget).1.D ≤ _ at hD
  have hOwner := GeneralPaperEqualIntegerCallerLifetime.all_phases model W A exponent values v hv small budget .returned
  change borrowed true model W A exponent values v hv small budget ≤ _ at hOwner
  have hKernel := GeneralPaperEqualPowerWidthLifetime.all_phases model A
    (actual true model W A exponent values v hv small budget).1.D _ (exponent + 5)
    (borrowed true model W A exponent values v hv small budget) hD phase
  exact hKernel.trans (GeneralPaperEqualPowerWidthLifetime.borrowed_mono model A _ _ _ _ hOwner)

theorem source_prices {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    let result := (GeneralPaperEqualAddressedPreparation.run bits model W A exponent values v hv small budget).2
    (GeneralPaperEqualPowerWidthLifetime.power model A (exponent + 5)).2 + 128 * A + 128 = result.1.1.midpointPower ∧
      (GeneralPaperEqualPowerWidthLifetime.width model A (actual bits model W A exponent values v hv small budget).1.D).2 = result.1.2.1 := by
  simp only [GeneralPaperEqualPowerWidthLifetime.power, GeneralPaperEqualPowerWidthLifetime.width,
    actual, compacted, GeneralPaperEqualIntegerCallerLifetime.full, GeneralPaperEqualSegmentCallerLifetime.segmentReturn,
    GeneralPaperEqualAddressedPreparation.run, GeneralPaperEqualAddressedClosure.run, GeneralPaperEqualMeasuredClosure.make]
  exact ⟨True.intro, True.intro⟩

end Blotto.GeneralPaperEqualPowerWidthCaller
