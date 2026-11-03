import Blotto.GeneralPaperStoredAllocationWork
import Blotto.GeneralPaperStoredNativeRejectionBound

/-! A scalar-parameter majorant for the complete actual grouped inner draw.
The native producer supplies seven rows, at most three groups and short
control/endpoint/route parameters; no analysis bound executes in the draw. -/
namespace Blotto.GeneralPaperStoredDrawMajorant
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualRejectionTraceMeasure
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def bound (model : RationalCostModel) (A n m w P K s b c : ℕ) : ℕ :=
  GeneralPaperStoredSamplerRejectionWork.expectedBound model A w 7 7 +
    GeneralPaperStoredSamplerMidpointWork.majorant model A P K +
    GeneralPaperStoredSamplerGroupsWork.runBound model A m s b K +
    GeneralPaperStoredEmissionWork.samplerBound model A n m (GeneralPaperStoredPostselectionWork.emissionHeight s b c K) + 384 * (A + 1)

def nativeBound (model : RationalCostModel) (A n k b : ℕ) : ℕ :=
  bound model A n 3 (GeneralPaperStoredNativeRejectionBound.wordBound n k)
    (3670016 * GeneralPaperEqualNativeRetainedStorage.short n k + 3) (k + 5)
    (GeneralPaperEqualNativeSampler.segmentHeight n k) b (binaryWordWidth n + k + 9)

theorem groups_mono (model : RationalCostModel) (A n m M w P K s b c : ℕ) (hm : m ≤ M) :
    bound model A n m w P K s b c ≤ bound model A n M w P K s b c := by
  have hWord := binaryWordWidth_mono hm
  unfold bound GeneralPaperStoredSamplerGroupsWork.runBound GeneralPaperStoredPreparedGroupsWork.bound
    GeneralPaperStoredEndpointWork.heightBound GeneralPaperStoredInterpolationWork.bound
    GeneralPaperStoredEmissionWork.samplerBound GeneralPaperStoredEmissionWork.preparedBound
    GeneralPaperStoredRouteEmissionWork.bound GeneralPaperStoredRouteEmissionWork.collectBound
    GeneralPaperStoredRouteCoordinateWork.bound GeneralPaperStoredRouteArrayWork.heightBound
    GeneralPaperEncodedScalarStorage.natBits
  gcongr

theorem native_expected {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (returned : Installed (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget).address)
    (hReturn : (GeneralPaperCountedSamplerInstallation.build model S
      (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget)).values = some returned) :
    let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    (∫⁻ trace, ((GeneralPaperStoredAllocationLaw.observed model source.address returned source.prepared.D source.prepared.midpointBits trace).work : ℝ≥0∞)
      ∂(law source.prepared.D source.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive source.prepared) :
        Measure (Trace source.prepared.D source.prepared.midpointBits))) ≤
      (nativeBound model source.address n k (rationalWordWidth budget) : ℝ≥0∞) := by
  dsimp only
  let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
  let m := (GeneralPaperEqualFiniteKernel.terminal (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv) small).groups.length
  have hExpected := GeneralPaperStoredAllocationWork.native_expected bits model W S k values v hv small budget returned hReturn
  have hCount := GeneralPaperEqualNativeCache.compact_count (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv) small
  have hWidth := GeneralPaperEqualNativeCache.rangeBits bits model W k values v hv small budget
  have hRows : source.categorical.rows.length ≤ 7 := by rw [GeneralPaperEqualBooleanCache.rows_length]; exact hCount.2
  have hReject := GeneralPaperStoredNativeRejectionBound.monotone model source.address source.prepared.rangeBits _ source.categorical.rows.length
    (GeneralPaperStoredNativeRejectionBound.wordBound n k) 7 7 hWidth hCount.2 hRows
  have hMidpoint := GeneralPaperStoredSamplerMidpointWork.native_majorant bits model W k values v hv small budget
  change GeneralPaperStoredSamplerMidpointWork.bound model source.address source.prepared ≤
    GeneralPaperStoredSamplerMidpointWork.majorant model source.address (3670016 * GeneralPaperEqualNativeRetainedStorage.short n k + 3) (k + 5) at hMidpoint
  have hK : source.prepared.midpointBits = k + 5 := rfl
  have hCompare : GeneralPaperStoredAllocationWork.expectedBound model source.address
      (GeneralPaperEqualNativeSampler.segmentHeight n k) (rationalWordWidth budget) (binaryWordWidth n + k + 9) source ≤
      bound model source.address n m (GeneralPaperStoredNativeRejectionBound.wordBound n k)
        (3670016 * GeneralPaperEqualNativeRetainedStorage.short n k + 3) (k + 5)
        (GeneralPaperEqualNativeSampler.segmentHeight n k) (rationalWordWidth budget) (binaryWordWidth n + k + 9) := by
    unfold GeneralPaperStoredAllocationWork.expectedBound GeneralPaperStoredPostselectionWork.bound
      GeneralPaperStoredSamplerGroupsWork.drawBound bound
    rw [hK]
    dsimp only [m]
    omega
  have hGroups := groups_mono model source.address n m 3 (GeneralPaperStoredNativeRejectionBound.wordBound n k)
    (3670016 * GeneralPaperEqualNativeRetainedStorage.short n k + 3) (k + 5)
    (GeneralPaperEqualNativeSampler.segmentHeight n k) (rationalWordWidth budget) (binaryWordWidth n + k + 9)
    (GeneralPaperEqualNativeCache.group_count _ small)
  exact hExpected.trans (by exact_mod_cast hCompare.trans hGroups)

end Blotto.GeneralPaperStoredDrawMajorant
