import Blotto.GeneralPaperEncodedOptionCache

/-! The entire retained Ready cache includes alphabet controls, summary
family, four catalogue array families, exact tags and all cached tail plans.
Only the actual incoming summary code words remain a caller premise. -/
namespace Blotto.GeneralPaperEncodedOptimizerCache
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def alphabetFootprint (W : ℕ) (a : Alphabet) : ℕ :=
  (1+binaryWordWidth a.D)+(1+binaryWordWidth a.C)+(1+binaryWordWidth a.lambda)+64*W

theorem alphabet_bound (W : ℕ) (a : Alphabet) : alphabetFootprint W a≤3*GeneralPaperDecoderControls.operandWidth a.lambda+64*W := by
  have h := GeneralPaperEpochCacheCodeWords.alphabet_scalars a
  unfold alphabetFootprint
  omega

def summaryProfile (W m lambda k : ℕ) : ℕ :=
  m*((GeneralPaperSourceParameters.prepare k).summarySize*(GeneralPaperDecoderControls.operandWidth lambda+W)+32*W+W)+32*W

theorem summary_family {m k : ℕ} (W lambda : ℕ) (values : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Summary k))
    (hw : ∀ j i,1+binaryWordWidth ((values.read j).read i)≤GeneralPaperDecoderControls.operandWidth lambda) :
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) values≤summaryProfile W m lambda k :=
  GeneralPaperEncodedFixedVector.bounded W _ (GeneralPaperEncodedNatArray.footprint W) values
    (fun j => GeneralPaperEncodedNatArray.bounded W _ (values.read j) (hw j))

def footprint {m k : ℕ} (W : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k) : ℕ :=
  alphabetFootprint W ready.alphabet+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) ready.summaries+
    GeneralPaperEncodedCatalogueStorage.footprint W ready.data+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedOptionCache.footprint W) ready.cached+1+128*W

def profile (W m lambda k : ℕ) : ℕ :=
  let L := GeneralPaperDecoderControls.operandWidth lambda
  let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
  (3*L+64*W)+summaryProfile W m lambda k+GeneralPaperEncodedCatalogueStorage.profile W m K L+
    (m*(GeneralPaperEncodedOptionCache.profile W L K k+W)+32*W)+1+128*W

theorem bounded {m k : ℕ} (W : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (hw : ∀ j i,1+binaryWordWidth ((ready.summaries.read j).read i)≤GeneralPaperDecoderControls.operandWidth ready.alphabet.lambda) :
    footprint W ready≤profile W m ready.alphabet.lambda k := by
  have ha := alphabet_bound W ready.alphabet
  have hs := summary_family W ready.alphabet.lambda ready.summaries hw
  have hd := GeneralPaperEncodedCatalogueStorage.ready_data W ready
  have hc := GeneralPaperEncodedFixedVector.bounded W _ (GeneralPaperEncodedOptionCache.footprint W) ready.cached
    (GeneralPaperEncodedOptionCache.ready_field W ready)
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ha hs) hd) hc) 1) (128*W)

theorem candidate {m k : ℕ} (W : ℕ) (cache : GeneralPaperCatalogueEpochCache.Cache m k)
    (hc : GeneralPaperCatalogueEpochMetadata.CodesValid cache) :
    footprint W cache.candidate≤profile W m cache.alphabet.lambda k := by
  have ha : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  have hs : cache.candidate.summaries=cache.lambda := by rw [cache.candidate_spec]; rfl
  have hw (j : Fin m) (i : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
      1+binaryWordWidth ((cache.candidate.summaries.read j).read i)≤GeneralPaperDecoderControls.operandWidth cache.candidate.alphabet.lambda := by
    rw [ha,hs]
    exact GeneralPaperEpochCacheCodeWords.summary_word cache hc .lambda j i
  have h := bounded W cache.candidate hw
  rw [ha] at h
  exact h

theorem response {m k : ℕ} (W : ℕ) (cache : GeneralPaperCatalogueEpochCache.Cache m k)
    (hc : GeneralPaperCatalogueEpochMetadata.CodesValid cache) :
    footprint W cache.response≤profile W m cache.alphabet.lambda k := by
  have ha : cache.response.alphabet=cache.alphabet := by rw [cache.response_spec]; rfl
  have hs : cache.response.summaries=cache.mu := by rw [cache.response_spec]; rfl
  have hw (j : Fin m) (i : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
      1+binaryWordWidth ((cache.response.summaries.read j).read i)≤GeneralPaperDecoderControls.operandWidth cache.response.alphabet.lambda := by
    rw [ha,hs]
    exact GeneralPaperEpochCacheCodeWords.summary_word cache hc .mu j i
  have h := bounded W cache.response hw
  rw [ha] at h
  exact h

end Blotto.GeneralPaperEncodedOptimizerCache
