import Blotto.GeneralPaperEqualFirstFinalClosureSpace

/-! All corrected grouped preparation phases, from first rounding through
the actual returned sampler. Each transition retains the proved caller owners.
The phase indices use the source's actual groups, compact count and width;
the midpoint power index remains k+5. -/
namespace Blotto.GeneralPaperEqualFirstPreparationSpace
open GeneralPaperEqualFirstNativeFacts (rounded)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

inductive Phase (n m c K width : ℕ) where
  | source (phase : GeneralPaperEqualFirstSourceSpace.Phase n m)
  | segment (phase : GeneralPaperNativeSegmentFactoryLifetime.Phase m)
  | compaction (phase : GeneralPaperCompactionLifetime.Phase c)
  | integerData (phase : GeneralPaperCategoricalIntegerLifetime.Phase c)
  | powerWidth (phase : GeneralPaperEqualPowerWidthLifetime.Phase K)
  | booleanCache (phase : GeneralPaperBooleanCacheLifetime.Phase width)
  | finalClosure (phase : GeneralPaperEqualFinalClosureLifetime.Phase)

def window {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    Phase n (terminal (rounded true model W k values v hv) small).groups.length
      (count (lottery (rounded true model W k values v hv) small)) (k+5)
      (GeneralPaperEqualFirstNativeCache.prepare true model W k values v hv small budget).rangeBits → ℕ
  | .source phase => GeneralPaperEqualFirstSourceSpace.window model W A k values v hv small budget phase
  | .segment phase => GeneralPaperEqualFirstSegmentCallerSpace.window model W A k values v hv small budget phase
  | .compaction phase => GeneralPaperEqualFirstIntegerCallerSpace.compactionWindow model W A k values v hv small budget phase
  | .integerData phase => GeneralPaperEqualFirstIntegerCallerSpace.window model W A k values v hv small budget phase
  | .powerWidth phase => GeneralPaperEqualFirstPowerBooleanSpace.powerWindow model W A k values v hv small budget phase
  | .booleanCache phase => GeneralPaperEqualFirstPowerBooleanSpace.window model W A k values v hv small budget phase
  | .finalClosure phase => GeneralPaperEqualFirstFinalClosureSpace.window model W A k values v hv small budget phase

def profile {n : ℕ} (model : RationalCostModel) (W A k m c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperEqualFirstSourceSpace.profile model W A k m values budget+
    GeneralPaperEqualFirstSegmentCallerSpace.profile model W A k m values budget+
    GeneralPaperEqualFirstIntegerCallerSpace.compactionProfile model W A k m c values budget+
    GeneralPaperEqualFirstIntegerCallerSpace.profile model W A k m c values budget+
    GeneralPaperEqualFirstPowerBooleanSpace.powerProfile model W A k m c values budget+
    GeneralPaperEqualFirstPowerBooleanSpace.profile model W A k m c width values budget+
    GeneralPaperEqualFirstFinalClosureSpace.profile model W A k m c width values budget

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : Phase n (terminal (rounded true model W k values v hv) small).groups.length
      (count (lottery (rounded true model W k values v hv) small)) (k+5)
      (GeneralPaperEqualFirstNativeCache.prepare true model W k values v hv small budget).rangeBits) :
    window model W A k values v hv small budget phase ≤
      profile model W A k (terminal (rounded true model W k values v hv) small).groups.length
        (count (lottery (rounded true model W k values v hv) small))
        (GeneralPaperEqualFirstNativeCache.prepare true model W k values v hv small budget).rangeBits values budget := by
  cases phase with
  | source phase =>
    have h := GeneralPaperEqualFirstSourceSpace.all_phases model W A k values v hv small budget phase
    simp only [window,profile]
    omega
  | segment phase =>
    have h := GeneralPaperEqualFirstSegmentCallerSpace.all_phases model W A k values v hv small budget phase
    simp only [window,profile]
    omega
  | compaction phase =>
    have h := GeneralPaperEqualFirstIntegerCallerSpace.compaction_phases model W A k values v hv small budget phase
    simp only [window,profile]
    omega
  | integerData phase =>
    have h := GeneralPaperEqualFirstIntegerCallerSpace.all_phases model W A k values v hv small budget phase
    simp only [window,profile]
    omega
  | powerWidth phase =>
    have h := GeneralPaperEqualFirstPowerBooleanSpace.power_phases model W A k values v hv small budget phase
    simp only [window,profile]
    omega
  | booleanCache phase =>
    have h := GeneralPaperEqualFirstPowerBooleanSpace.all_phases model W A k values v hv small budget phase
    simp only [window,profile]
    omega
  | finalClosure phase =>
    have h := GeneralPaperEqualFirstFinalClosureSpace.all_phases model W A k values v hv small budget phase
    simp only [window,profile]
    omega

end Blotto.GeneralPaperEqualFirstPreparationSpace
