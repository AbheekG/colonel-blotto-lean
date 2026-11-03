import Blotto.GeneralPaperEqualFirstIntegerCallerSpace

/-! Actual k+5 midpoint power, rejection-width discovery and Boolean cache
construction. The integer return and all earlier callers stay live. Canonical
cache equality transports phase indices only, with no execution replay. -/
namespace Blotto.GeneralPaperEqualFirstPowerBooleanSpace
open GeneralPaperEqualFirstNativeFacts (rounded segmentHeight)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperPositiveSegmentCompaction (count)
open GeneralPaperEqualFirstIntegerCallerSpace (actual compacted)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def powerBorrowed {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  GeneralPaperEqualFirstIntegerCallerSpace.window model W A k values v hv small budget .returned

def powerWindow {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperEqualPowerWidthLifetime.Phase (k+5)) : ℕ :=
  GeneralPaperEqualPowerWidthLifetime.window model A (actual model W A k values v hv small).1.D (k+5)
    (powerBorrowed model W A k values v hv small budget) phase

def powerProfile {n : ℕ} (model : RationalCostModel) (W A k m c : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperEqualPowerWidthLifetime.profile model A (segmentHeight n k*c+1) (k+5)
    (GeneralPaperEqualFirstIntegerCallerSpace.profile model W A k m c values budget)

theorem integer_denominator {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) :
    binaryWordWidth (actual model W A k values v hv small).1.D ≤
      segmentHeight n k*count (lottery (rounded true model W k values v hv) small)+1 := by
  let p := (compacted model W A k values v hv small).1
  have hl := GeneralPaperPositiveSegmentCompaction.compact_height
    (lottery (rounded true model W k values v hv) small)
    (GeneralPaperEqualFirstNativeFacts.native_lottery_height true model W k values v hv small)
  exact GeneralPaperEqualPowerWidthCaller.integer_denominator_word p model A (by
    intro i; rw [p.weight_correct]; exact hl.1 i)

theorem power_phases {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperEqualPowerWidthLifetime.Phase (k+5)) :
    powerWindow model W A k values v hv small budget phase ≤
      powerProfile model W A k (terminal (rounded true model W k values v hv) small).groups.length
        (count (lottery (rounded true model W k values v hv) small)) values budget := by
  have hD := integer_denominator model W A k values v hv small
  have hOwner := GeneralPaperEqualFirstIntegerCallerSpace.all_phases model W A k values v hv small budget .returned
  have h := GeneralPaperEqualPowerWidthLifetime.all_phases model A
    (actual model W A k values v hv small).1.D _ (k+5)
    (powerBorrowed model W A k values v hv small budget) hD phase
  exact h.trans (GeneralPaperEqualPowerWidthLifetime.borrowed_mono model A _ _ _ _ hOwner)

def prepared {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :=
  (GeneralPaperEqualMeasuredClosure.make
    (GeneralPaperEqualFirstRouteCallerLifetime.routes model W A k values v hv small).1
    (compacted model W A k values v hv small).1 model A (k+5) budget).1

theorem prepared_eq {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    prepared model W A k values v hv small budget = GeneralPaperEqualFirstNativeCache.prepare true model W k values v hv small budget :=
  GeneralPaperEqualMeasuredClosure.make_data _ _ model A (k+5) budget

def sourcePhase {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperBooleanCacheLifetime.Phase (GeneralPaperEqualFirstNativeCache.prepare true model W k values v hv small budget).rangeBits) :
    GeneralPaperBooleanCacheLifetime.Phase (prepared model W A k values v hv small budget).rangeBits := by
  rw [prepared_eq]
  exact phase

def borrowed {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  powerWindow model W A k values v hv small budget .returned

def window {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperBooleanCacheLifetime.Phase (GeneralPaperEqualFirstNativeCache.prepare true model W k values v hv small budget).rangeBits) : ℕ :=
  GeneralPaperBooleanCacheLifetime.window (prepared model W A k values v hv small budget) model A
    (borrowed model W A k values v hv small budget) (sourcePhase model W A k values v hv small budget phase)

def profile {n : ℕ} (model : RationalCostModel) (W A k m c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperBooleanCacheLifetime.profile model A c width (segmentHeight n k*c+1)
    (powerProfile model W A k m c values budget)

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperBooleanCacheLifetime.Phase (GeneralPaperEqualFirstNativeCache.prepare true model W k values v hv small budget).rangeBits) :
    window model W A k values v hv small budget phase ≤
      profile model W A k (terminal (rounded true model W k values v hv) small).groups.length
        (count (lottery (rounded true model W k values v hv) small))
        (GeneralPaperEqualFirstNativeCache.prepare true model W k values v hv small budget).rangeBits values budget := by
  have hD := GeneralPaperEqualPreparedCache.denominator_word
    (GeneralPaperEqualFirstNativeCache.prepare true model W k values v hv small budget)
    (GeneralPaperEqualFirstNativeFacts.native_lottery_height true model W k values v hv small)
  rw [← prepared_eq model W A k values v hv small budget] at hD
  have h := GeneralPaperBooleanCacheLifetime.all_phases (prepared model W A k values v hv small budget) model A _
    (borrowed model W A k values v hv small budget) hD (sourcePhase model W A k values v hv small budget phase)
  have hOwner := power_phases model W A k values v hv small budget .returned
  have hb := h.trans (GeneralPaperBooleanCacheLifetime.borrowed_mono model A _ _ _ _ _ hOwner)
  have he := congrArg (fun w => GeneralPaperBooleanCacheLifetime.profile model A
    (count (lottery (rounded true model W k values v hv) small)) w
    (segmentHeight n k*count (lottery (rounded true model W k values v hv) small)+1)
    (powerProfile model W A k (terminal (rounded true model W k values v hv) small).groups.length
      (count (lottery (rounded true model W k values v hv) small)) values budget))
    (congrArg (fun p => p.rangeBits) (prepared_eq model W A k values v hv small budget))
  exact hb.trans_eq he

end Blotto.GeneralPaperEqualFirstPowerBooleanSpace
