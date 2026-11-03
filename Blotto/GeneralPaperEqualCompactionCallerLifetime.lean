import Blotto.GeneralPaperCompactionLifetime

/-! Positive compaction of the actual native full segment return. Its caller
retains original/prefix/code owners, full rows and the segment price record.
The previously proved native resident profile is a conservative bound; no
completed compact descriptor is assumed present during this construction. -/
namespace Blotto.GeneralPaperEqualCompactionCallerLifetime
open GeneralPaperEqualNativeSampler (rounded segmentHeight)
open GeneralPaperEqualFiniteKernel (lottery)
open GeneralPaperEqualIntegerCallerLifetime (full)
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 1800000

def borrowed {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  GeneralPaperEqualSegmentCallerLifetime.borrowed bits model W A exponent values v hv small budget +
    GeneralPaperEqualRetainedStorage.segmentFoot A (full bits model W A exponent values v hv small budget).1 +
    natBits (full bits model W A exponent values v hv small budget).2 + 128 * A

theorem pre_owner_le (A B fullFoot compactFoot fullWork compactWork : ℕ) :
    B + fullFoot + natBits fullWork + 128 * A ≤
      B + fullFoot + compactFoot + fields A [fullWork, compactWork] + 256 * A := by
  simp only [fields, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
  omega

theorem borrowed_bound {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    borrowed true model W A exponent values v hv small budget ≤
      GeneralPaperEqualIntegerCallerLifetime.residentProfile model W A exponent values budget := by
  have hPre : borrowed true model W A exponent values v hv small budget ≤
      GeneralPaperEqualIntegerCallerLifetime.resident true model W A exponent values v hv small budget := by
    unfold borrowed GeneralPaperEqualIntegerCallerLifetime.resident
    exact pre_owner_le _ _ _ _ _ _
  exact hPre.trans (GeneralPaperEqualIntegerCallerLifetime.resident_bound model W A exponent values v hv small budget)

def window {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperCompactionLifetime.Phase (GeneralPaperPositiveSegmentCompaction.count
      (lottery (rounded bits model W exponent values v hv) small))) : ℕ :=
  GeneralPaperCompactionLifetime.window (full bits model W A exponent values v hv small budget).1 model A
    (borrowed bits model W A exponent values v hv small budget) phase

def profile {n : ℕ} (model : RationalCostModel) (W A exponent c : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperCompactionLifetime.profile model A c 9 (segmentHeight n exponent)
    (GeneralPaperEqualIntegerCallerLifetime.residentProfile model W A exponent values budget)

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperCompactionLifetime.Phase (GeneralPaperPositiveSegmentCompaction.count
      (lottery (rounded true model W exponent values v hv) small))) :
    window true model W A exponent values v hv small budget phase ≤
      profile model W A exponent (GeneralPaperPositiveSegmentCompaction.count
        (lottery (rounded true model W exponent values v hv) small)) values budget := by
  have hHeight := GeneralPaperEqualNativeSampler.native_lottery_height true model W exponent values v hv small
  have hs : 2 ≤ segmentHeight n exponent := by
    norm_num [segmentHeight, GeneralPaperEqualNativeSampler.fieldHeight, expressionHeightBudget]
    omega
  have hKernel := GeneralPaperCompactionLifetime.all_phases
    (full true model W A exponent values v hv small budget).1 model A
    (borrowed true model W A exponent values v hv small budget) hs hHeight.1 phase
  exact hKernel.trans (GeneralPaperCompactionLifetime.borrowed_mono model A _ _ _ _ _
    (borrowed_bound model W A exponent values v hv small budget))

end Blotto.GeneralPaperEqualCompactionCallerLifetime
