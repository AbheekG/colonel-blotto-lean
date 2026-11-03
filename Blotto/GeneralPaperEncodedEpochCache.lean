import Blotto.GeneralPaperEncodedOptimizerCache

/-! The full retained epoch cache owns four summary families, both Ready
objects and all eight-plan field records. Actual native code validity closes
every coordinate-word premise, including all nested work annotations. -/
namespace Blotto.GeneralPaperEncodedEpochCache
open GeneralPaperCatalogueEpochCache
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def footprint {m k : ℕ} (W : ℕ) (cache : Cache m k) : ℕ :=
  GeneralPaperEncodedOptimizerCache.alphabetFootprint W cache.alphabet+
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) cache.p+
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) cache.q+
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) cache.lambda+
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) cache.mu+
  GeneralPaperEncodedOptimizerCache.footprint W cache.candidate+GeneralPaperEncodedOptimizerCache.footprint W cache.response+
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedFieldPlanStorage.footprint W) cache.plans+128*W

def profile (W m lambda k : ℕ) : ℕ :=
  (3*GeneralPaperDecoderControls.operandWidth lambda+64*W)+4*GeneralPaperEncodedOptimizerCache.summaryProfile W m lambda k+
    2*GeneralPaperEncodedOptimizerCache.profile W m lambda k+
    (m*(GeneralPaperEncodedFieldPlanStorage.profile W lambda k+W)+32*W)+128*W

theorem bounded {m k : ℕ} (W : ℕ) (cache : Cache m k) (hc : GeneralPaperCatalogueEpochMetadata.CodesValid cache) :
    footprint W cache≤profile W m cache.alphabet.lambda k := by
  have ha := GeneralPaperEncodedOptimizerCache.alphabet_bound W cache.alphabet
  have hp := GeneralPaperEncodedOptimizerCache.summary_family W cache.alphabet.lambda cache.p
    (GeneralPaperEpochCacheCodeWords.summary_word cache hc .p)
  have hq := GeneralPaperEncodedOptimizerCache.summary_family W cache.alphabet.lambda cache.q
    (GeneralPaperEpochCacheCodeWords.summary_word cache hc .q)
  have hl := GeneralPaperEncodedOptimizerCache.summary_family W cache.alphabet.lambda cache.lambda
    (GeneralPaperEpochCacheCodeWords.summary_word cache hc .lambda)
  have hu := GeneralPaperEncodedOptimizerCache.summary_family W cache.alphabet.lambda cache.mu
    (GeneralPaperEpochCacheCodeWords.summary_word cache hc .mu)
  have hca := GeneralPaperEncodedOptimizerCache.candidate W cache hc
  have hra := GeneralPaperEncodedOptimizerCache.response W cache hc
  have hPlans := GeneralPaperEncodedFixedVector.bounded W _ (GeneralPaperEncodedFieldPlanStorage.footprint W) cache.plans
    (GeneralPaperEncodedFieldPlanStorage.actual W cache hc)
  have h := Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ha hp) hq) hl) hu) hca) hra) hPlans) (128*W)
  exact h.trans_eq (by unfold profile; ring)

end Blotto.GeneralPaperEncodedEpochCache
