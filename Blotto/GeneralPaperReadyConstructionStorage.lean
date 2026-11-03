import Blotto.GeneralPaperOptionPlanConstructionStorage

/-! The actual Ready constructor joins catalogue projections, native tags,
signed-tail option plans and its full return. Native data and decoder bounds
discharge all tag/plan premises; caller controls and mesh stay literal. -/
namespace Blotto.GeneralPaperReadyConstructionStorage
open GeneralPaperCodeAlphabet GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperCatalogueProjection (Field)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def arrays {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) :=
  (GeneralPaperCatalogueArraysExecution.run true (fun w => w) model W a response summaries).1

def tags {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) :=
  (GeneralPaperCatalogueTagFamily.run true (fun w => w) model.rat W (arrays model W a response summaries)).1

def ready {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :=
  (GeneralPaperCatalogueOptimizerPreparation.run true (fun w => w) model W k mesh a response summaries hm).1

theorem tag_words {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    rationalWordWidth (((tags model W a response summaries).read j).read i).threshold≤GeneralPaperDecoderControls.operandWidth a.lambda := by
  have hb := GeneralPaperCatalogueTagValue.native_bounds a response k summaries (arrays model W a response summaries)
    (GeneralPaperCatalogueArraysExecution.native_data true (fun w => w) model W k a response summaries) j i
  have hw := (GeneralPaperCatalogueTagValue.words a (((arrays model W a response summaries).thresholds.read j).read i) hb.1 hb.2).2.2
  unfold tags
  rw [GeneralPaperCatalogueTagFamily.data]
  unfold GeneralPaperCatalogueArrays.tags GeneralPaperNativeRowBudget.tags
  simp only [FixedArrayTable.read_ofFn]
  exact hw

theorem code_bound {m k : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    (((arrays model W a response summaries).codes.read j).read i)≤8*a.C := by
  unfold arrays
  rw [GeneralPaperCatalogueArraysExecution.native_data]
  exact (GeneralPaperCatalogueArrays.code_bound a response k summaries j i).le

theorem summary_word {m k : ℕ} (a : Alphabet) (summaries : FixedArrayTable m (Summary k))
    (hs : ∀ j r,(summaries.read j).read r<2*(8*a.C)) (j : Fin m) (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    natBits ((summaries.read j).read r)≤GeneralPaperDecoderControls.operandWidth a.lambda := by
  have h := (Nat.add_le_add_left (binaryWordWidth_mono (hs j r).le) 1).trans (GeneralPaperCataloguePartitionStorage.source_payload a)
  unfold GeneralPaperDecoderControls.operandWidth
  exact h.trans (by omega)

theorem returned {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hs : ∀ j r,(summaries.read j).read r<2*(8*a.C)) :
    GeneralPaperEncodedOptimizerCache.footprint W (ready model W mesh a response summaries hm)≤
      GeneralPaperEncodedOptimizerCache.profile W m a.lambda k :=
  GeneralPaperEncodedOptimizerCache.bounded W _ (summary_word a summaries hs)

def window {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (count rowCount tailCount : ℕ) (hc : count≤m) (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) : ℕ :=
  GeneralPaperTagFamilyStorage.familyWindow model W (arrays model W a response summaries) count rowCount hc hr j i+
    GeneralPaperOptionPlanConstructionStorage.window model W k (8*a.C) mesh summaries
      (arrays model W a response summaries).codes (tags model W a response summaries) count tailCount hc ht j q+
    GeneralPaperEncodedOptimizerCache.footprint W (ready model W mesh a response summaries hm)+
    fields W [8,a.C,8*a.C,k,mesh,m,(GeneralPaperSourceParameters.prepare k).summarySize+2]+
    (GeneralPaperCatalogueOptimizerPreparation.run true (fun w => w) model W k mesh a response summaries hm).2+256*W

def profile (model : RationalCostModel) (W m k mesh : ℕ) (a : Alphabet) : ℕ :=
  let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
  GeneralPaperTagFamilyStorage.familyProfile model W m K a.lambda+
    GeneralPaperOptionPlanConstructionStorage.profile model W m K k (8*a.C) mesh (GeneralPaperDecoderControls.operandWidth a.lambda)+
    GeneralPaperEncodedOptimizerCache.profile W m a.lambda k+
    fields W [8,a.C,8*a.C,k,mesh,m,K]+GeneralPaperCatalogueOptimizerPreparation.profile model W m k a+256*W

theorem bounded {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hs : ∀ j r,(summaries.read j).read r<2*(8*a.C))
    (count rowCount tailCount : ℕ) (hc : count≤m) (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) :
    window model W mesh a response summaries hm count rowCount tailCount hc hr ht j i q≤profile model W m k mesh a := by
  have htags := GeneralPaperTagFamilyStorage.family_bound model W (ready model W mesh a response summaries hm) count rowCount hc hr j i
  change GeneralPaperTagFamilyStorage.familyWindow model W (arrays model W a response summaries) count rowCount hc hr j i≤
    GeneralPaperTagFamilyStorage.familyProfile model W m ((GeneralPaperSourceParameters.prepare k).summarySize+2) a.lambda at htags
  have hplans := GeneralPaperOptionPlanConstructionStorage.bounded model W k (8*a.C) mesh (GeneralPaperDecoderControls.operandWidth a.lambda)
    summaries (arrays model W a response summaries).codes (tags model W a response summaries) (fun j r => (hs j r).le)
    (code_bound model W a response summaries) (tag_words model W a response summaries) hm count tailCount hc ht j q
  have hready := returned model W mesh a response summaries hm hs
  have hwork := GeneralPaperCatalogueOptimizerPreparation.bit_work model W k mesh a response summaries hm hs
  dsimp only [window,profile]
  omega

theorem with_catalogue_constructor {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (Summary k)) (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hs : ∀ j r,(summaries.read j).read r<2*(8*a.C)) (field : Field)
    (count copied rowCount tailCount : ℕ) (hc : count≤m) (hd : copied≤m)
    (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1))
    (used rowCopied partCount rawCount padCount : ℕ)
    (hp : partCount≤(GeneralPaperCachedCatalogueStorage.part a (summaries.read j)).count)
    (hraw : rawCount≤(GeneralPaperCachedCatalogueStorage.part a (summaries.read j)).count)
    (hpad : padCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2) :
    window model W mesh a response summaries hm count rowCount tailCount hc hr ht j i q+
      (GeneralPaperCatalogueArrayConstructionStorage.window model W a response summaries field count copied rowCount hc hd hr j+
        GeneralPaperCachedCatalogueStorage.window model W a response (summaries.read j) used rowCopied partCount rawCount padCount hp hraw hpad)≤
    profile model W m k mesh a+(GeneralPaperCatalogueArrayConstructionStorage.profile model W m
      (GeneralPaperSourceParameters.prepare k).summarySize a+GeneralPaperCachedCatalogueStorage.profile model W
        (GeneralPaperSourceParameters.prepare k).summarySize a) :=
  Nat.add_le_add (bounded model W mesh a response summaries hm hs count rowCount tailCount hc hr ht j i q)
    (GeneralPaperCatalogueArrayConstructionStorage.with_cached_constructor model W a response summaries hs field count copied rowCount hc hd hr j
      used rowCopied partCount rawCount padCount hp hraw hpad)

end Blotto.GeneralPaperReadyConstructionStorage
