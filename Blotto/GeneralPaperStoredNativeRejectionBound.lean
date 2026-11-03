import Blotto.GeneralPaperStoredSamplerRejectionWork

/-! Native seven-segment and short range-word bounds instantiate complete
actual stored rejection work. The final expectation concerns the same
source-only constructor return, without supplied storage-fit hypotheses. -/
namespace Blotto.GeneralPaperStoredNativeRejectionBound
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualRejectionTraceMeasure
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def wordBound (n k : ℕ) : ℕ := 3670016 * (binaryWordWidth n + k + 10) + 1

theorem monotone (model : RationalCostModel) (A w r count W R countMax : ℕ)
    (hw : w ≤ W) (hr : r ≤ R) (hc : count ≤ countMax) :
    GeneralPaperStoredSamplerRejectionWork.expectedBound model A w r count ≤
      GeneralPaperStoredSamplerRejectionWork.expectedBound model A W R countMax := by
  have hWord := binaryWordWidth_mono (Nat.add_le_add_right hw 1)
  have hLabel := binaryWordWidth_mono hr
  unfold GeneralPaperStoredSamplerRejectionWork.expectedBound GeneralPaperStoredRejectionWork.perAttempt
    GeneralPaperStoredTrialWork.bound GeneralPaperStoredDenominatorWork.bound GeneralPaperStoredCacheCategoricalWork.bound
    GeneralPaperStoredCategoricalWork.bound GeneralPaperStoredCategoricalWork.perRow GeneralPaperStoredBooleanRowsWork.bound
    GeneralPaperStoredBooleanWordWork.bound GeneralPaperStoredBooleanWordWork.packedBound GeneralPaperStoredBitCollectionWork.bound
    GeneralPaperStoredFreshWork.bound GeneralPaperEncodedScalarStorage.natBits
  gcongr

theorem native_expected {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S k K : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (returned : Installed (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget).address)
    (hReturn : (GeneralPaperCountedSamplerInstallation.build model S
      (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget)).values = some returned) :
    let sampler := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    (∫⁻ trace, ((GeneralPaperStoredRejectionTrace.observed model sampler.address returned sampler.prepared.D K trace).work : ℝ≥0∞)
      ∂(law sampler.prepared.D K (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) : Measure (Trace sampler.prepared.D K))) ≤
      (GeneralPaperStoredSamplerRejectionWork.expectedBound model sampler.address (wordBound n k) 7 7 : ℝ≥0∞) := by
  dsimp only
  let sampler := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
  have hExpected := GeneralPaperStoredSamplerRejectionWork.native_expected bits model W S k K values v hv small budget returned hReturn
  have hWidth := GeneralPaperEqualNativeCache.rangeBits bits model W k values v hv small budget
  have hCount := GeneralPaperEqualNativeCache.compact_count (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv) small
  have hRows : sampler.categorical.rows.length ≤ 7 := by rw [GeneralPaperEqualBooleanCache.rows_length]; exact hCount.2
  have hBound := monotone model sampler.address sampler.prepared.rangeBits _ sampler.categorical.rows.length
    (wordBound n k) 7 7 hWidth hCount.2 hRows
  exact hExpected.trans (by exact_mod_cast hBound)

end Blotto.GeneralPaperStoredNativeRejectionBound
