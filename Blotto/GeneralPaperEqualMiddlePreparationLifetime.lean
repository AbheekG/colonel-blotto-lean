import Blotto.GeneralPaperEqualCompactionCallerLifetime

/-! One native preparation observer for consecutive segment-factory,
positive-compaction and categorical-integer phases. The same retained
prefix and exact measured returns connect them. Other preparation phases
are deliberately absent; this is not a whole-preparation space claim. -/
namespace Blotto.GeneralPaperEqualMiddlePreparationLifetime
open GeneralPaperEqualNativeSampler (rounded)
open GeneralPaperEqualFiniteKernel (lottery terminal)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 1800000

inductive Phase (m c : ℕ) where
  | segment (phase : GeneralPaperNativeSegmentFactoryLifetime.Phase m)
  | compaction (phase : GeneralPaperCompactionLifetime.Phase c)
  | integerData (phase : GeneralPaperCategoricalIntegerLifetime.Phase c)

def window {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    Phase (terminal (rounded bits model W exponent values v hv) small).groups.length
      (count (lottery (rounded bits model W exponent values v hv) small)) → ℕ
  | .segment phase => GeneralPaperEqualSegmentCallerLifetime.window bits model W A exponent values v hv small budget phase
  | .compaction phase => GeneralPaperEqualCompactionCallerLifetime.window bits model W A exponent values v hv small budget phase
  | .integerData phase => GeneralPaperEqualIntegerCallerLifetime.window bits model W A exponent values v hv small budget phase

def profile {n : ℕ} (model : RationalCostModel) (W A exponent c : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  max (GeneralPaperEqualSegmentCallerLifetime.profile model W A exponent values budget)
    (max (GeneralPaperEqualCompactionCallerLifetime.profile model W A exponent c values budget)
      (GeneralPaperEqualIntegerCallerLifetime.profile model W A exponent values budget c))

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : Phase (terminal (rounded true model W exponent values v hv) small).groups.length
      (count (lottery (rounded true model W exponent values v hv) small))) :
    window true model W A exponent values v hv small budget phase ≤
      profile model W A exponent (count (lottery (rounded true model W exponent values v hv) small)) values budget := by
  cases phase with
  | segment phase =>
    exact (GeneralPaperEqualSegmentCallerLifetime.actual model W A exponent values v hv small budget phase).trans
      (le_max_left _ _)
  | compaction phase =>
    exact (GeneralPaperEqualCompactionCallerLifetime.all_phases model W A exponent values v hv small budget phase).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  | integerData phase =>
    exact (GeneralPaperEqualIntegerCallerLifetime.all_phases model W A exponent values v hv small budget phase).trans
      ((le_max_right _ _).trans (le_max_right _ _))

end Blotto.GeneralPaperEqualMiddlePreparationLifetime
