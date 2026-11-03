import Blotto.GeneralPaperBooleanCacheLifetime

/-! The Boolean producer consumes the actual prepared-cache projection of
native addressed preparation. Its canonical equality is used only to bound
precision/phase indices; the observed source and prices remain the actual
constructor. All prior owners come from the proved power/width return. -/
namespace Blotto.GeneralPaperEqualBooleanCallerLifetime
open GeneralPaperEqualNativeSampler (rounded segmentHeight)
open GeneralPaperEqualFiniteKernel (lottery)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def prepared {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :=
  (GeneralPaperEqualAddressedPreparation.run bits model W A exponent values v hv small budget).1.prepared

theorem prepared_eq {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    prepared bits model W A exponent values v hv small budget =
      GeneralPaperEqualNativeCache.prepare bits model W exponent values v hv small budget := by
  unfold prepared
  rw [GeneralPaperEqualAddressedPreparation.data]
  rfl

def sourcePhase {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperBooleanCacheLifetime.Phase (GeneralPaperEqualNativeCache.prepare bits model W exponent values v hv small budget).rangeBits) :
    GeneralPaperBooleanCacheLifetime.Phase (prepared bits model W A exponent values v hv small budget).rangeBits := by
  rw [prepared_eq]
  exact phase

def borrowed {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  GeneralPaperEqualPowerWidthCaller.window bits model W A exponent values v hv small budget .returned

def window {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperBooleanCacheLifetime.Phase (GeneralPaperEqualNativeCache.prepare bits model W exponent values v hv small budget).rangeBits) : ℕ :=
  GeneralPaperBooleanCacheLifetime.window (prepared bits model W A exponent values v hv small budget) model A
    (borrowed bits model W A exponent values v hv small budget)
    (sourcePhase bits model W A exponent values v hv small budget phase)

def profile {n : ℕ} (model : RationalCostModel) (W A exponent c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperBooleanCacheLifetime.profile model A c width (segmentHeight n exponent * c + 1)
    (GeneralPaperEqualPowerWidthCaller.profile model W A exponent c values budget)

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperBooleanCacheLifetime.Phase (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits) :
    window true model W A exponent values v hv small budget phase ≤
      profile model W A exponent (count (lottery (rounded true model W exponent values v hv) small))
        (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits values budget := by
  have hHeight := GeneralPaperEqualNativeSampler.native_lottery_height true model W exponent values v hv small
  have hD := GeneralPaperEqualPreparedCache.denominator_word
    (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget) hHeight
  rw [← prepared_eq true model W A exponent values v hv small budget] at hD
  have hKernel := GeneralPaperBooleanCacheLifetime.all_phases
    (prepared true model W A exponent values v hv small budget) model A _
    (borrowed true model W A exponent values v hv small budget) hD
    (sourcePhase true model W A exponent values v hv small budget phase)
  have hOwner := GeneralPaperEqualPowerWidthCaller.all_phases model W A exponent values v hv small budget .returned
  have hBound := hKernel.trans (GeneralPaperBooleanCacheLifetime.borrowed_mono model A _ _ _ _ _ hOwner)
  have hProfile := congrArg (fun w => GeneralPaperBooleanCacheLifetime.profile model A
    (count (lottery (rounded true model W exponent values v hv) small)) w
    (segmentHeight n exponent * count (lottery (rounded true model W exponent values v hv) small) + 1)
    (GeneralPaperEqualPowerWidthCaller.profile model W A exponent
      (count (lottery (rounded true model W exponent values v hv) small)) values budget))
    (congrArg (fun p => p.rangeBits) (prepared_eq true model W A exponent values v hv small budget))
  exact hBound.trans_eq hProfile

theorem source_return_and_price {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    let result := GeneralPaperEqualAddressedPreparation.run bits model W A exponent values v hv small budget
    let actual := GeneralPaperStoredBooleanCache.run (prepared bits model W A exponent values v hv small budget) model A
    actual.1 = result.1.categorical ∧ actual.2 = result.2.1.2.2 := by
  simp only [prepared, GeneralPaperEqualAddressedPreparation.run, GeneralPaperEqualAddressedClosure.run]
  exact ⟨True.intro, True.intro⟩

end Blotto.GeneralPaperEqualBooleanCallerLifetime
