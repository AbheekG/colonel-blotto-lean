import Blotto.GeneralPaperFourSummaryConstructionStorage

/-! Native tree-to-epoch preparation retains produced summaries across the
summary-to-cache handoff, complete returned cache and caller controls.
Actual valid source trees derive all native summary/code premises. -/
namespace Blotto.GeneralPaperTreeEpochConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueOccurrenceHistory
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def arrays (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) :=
  (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc digits trees).1

theorem valid_four (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hv : Valid a k trees) (hp : Paths a k trees) :
    GeneralPaperEpochCacheConstructionStorage.ValidFour a (arrays model W m k Qv a c hc digits trees) :=
  GeneralPaperActualOccurrencePreparation.four_codes true (fun w => w) model.rat W m k Qv a c hc digits trees hv hp _ rfl

theorem returned (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hv : Valid a k trees) (hp : Paths a k trees) :
    GeneralPaperEncodedEpochCache.footprint W (GeneralPaperTreeEpochPreparation.run true (fun w => w) model W m k Qv a c hc digits trees).1≤
      GeneralPaperEncodedEpochCache.profile W m a.lambda k :=
  GeneralPaperEpochCacheConstructionStorage.returned model W c.controls.source.meshDenominator a
    (arrays model W m k Qv a c hc digits trees) (GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc)
    (valid_four model W m k Qv a c hc digits trees hv hp)

def window (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (count innerCount rowCount tailCount : ℕ)
    (hcount : count≤m) (hi : innerCount≤c.controls.source.summarySize)
    (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) (r : Fin c.controls.source.summarySize) (learner : Learner) : ℕ :=
  GeneralPaperFourSummaryConstructionStorage.window model W m k Qv a c hc digits trees count innerCount hcount hi r learner+
    GeneralPaperEpochCacheConstructionStorage.window model W c.controls.source.meshDenominator a (arrays model W m k Qv a c hc digits trees)
      (GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc) count rowCount tailCount hcount hr ht j i q+
    GeneralPaperEncodedEpochCache.footprint W (GeneralPaperTreeEpochPreparation.run true (fun w => w) model W m k Qv a c hc digits trees).1+
    fields W [m,k,a.lambda,a.lambda+1,digits,c.controls.source.meshDenominator,c.controls.source.summarySize]+256*W

def profile (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperFourSummaryConstructionStorage.profile model W m a.lambda k Qv+
    GeneralPaperEpochCacheConstructionStorage.profile model W m k (GeneralPaperSourceParameters.prepare k).meshDenominator a+
    GeneralPaperEncodedEpochCache.profile W m a.lambda k+
    fields W [m,k,a.lambda,a.lambda+1,GeneralPaperQuantileComparison.width a.lambda k,
      (GeneralPaperSourceParameters.prepare k).meshDenominator,(GeneralPaperSourceParameters.prepare k).summarySize]+256*W

theorem bounded (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (hd : digits=GeneralPaperQuantileComparison.width a.lambda k)
    (trees : Trees m a.lambda) (hv : Valid a k trees) (hp : Paths a k trees) (count innerCount rowCount tailCount : ℕ)
    (hcount : count≤m) (hi : innerCount≤c.controls.source.summarySize)
    (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) (r : Fin c.controls.source.summarySize) (learner : Learner) :
    window model W m k Qv a c hc digits trees count innerCount rowCount tailCount hcount hi hr ht j i q r learner≤profile model W m k Qv a := by
  have hs := GeneralPaperFourSummaryConstructionStorage.bounded model W m k Qv a c hc digits hd trees hv hp count innerCount hcount hi r learner
  have he := GeneralPaperEpochCacheConstructionStorage.bounded model W c.controls.source.meshDenominator a
    (arrays model W m k Qv a c hc digits trees) (GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc)
    (valid_four model W m k Qv a c hc digits trees hv hp) count rowCount tailCount hcount hr ht j i q
  have hout := returned model W m k Qv a c hc digits trees hv hp
  have hm := GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc
  have hn : c.controls.source.summarySize=(GeneralPaperSourceParameters.prepare k).summarySize := by rw [hc]; rfl
  have he' := he.trans_eq (show GeneralPaperEpochCacheConstructionStorage.profile model W m k c.controls.source.meshDenominator a=
      GeneralPaperEpochCacheConstructionStorage.profile model W m k (GeneralPaperSourceParameters.prepare k).meshDenominator a by rw [hm])
  have hctrl : fields W [m,k,a.lambda,a.lambda+1,digits,c.controls.source.meshDenominator,c.controls.source.summarySize]=
      fields W [m,k,a.lambda,a.lambda+1,GeneralPaperQuantileComparison.width a.lambda k,
        (GeneralPaperSourceParameters.prepare k).meshDenominator,(GeneralPaperSourceParameters.prepare k).summarySize] := by rw [hd,hm,hn]
  dsimp only [window,profile]
  omega

theorem with_field_row (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (hd : digits=GeneralPaperQuantileComparison.width a.lambda k)
    (trees : Trees m a.lambda) (hv : Valid a k trees) (hp : Paths a k trees) (count innerCount rowCount tailCount : ℕ)
    (hcount : count≤m) (hi : innerCount≤c.controls.source.summarySize)
    (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) (r : Fin c.controls.source.summarySize) (learner : Learner) :
    let x := arrays model W m k Qv a c hc digits trees
    let mesh := c.controls.source.meshDenominator
    let hm := GeneralPaperOptionPlanPrice.retained_mesh m a.lambda k Qv c hc
    window model W m k Qv a c hc digits trees count innerCount rowCount tailCount hcount hi hr ht j i q r learner+
      GeneralPaperFieldFamilyConstructionStorage.rowWindow model W a x
        (GeneralPaperEpochCacheConstructionStorage.candidate model W mesh a x hm).data.codes
        (GeneralPaperEpochCacheConstructionStorage.response model W mesh a x hm).data.codes j≤
      profile model W m k Qv a+GeneralPaperFieldFamilyConstructionStorage.rowProfile model W k a :=
  Nat.add_le_add (bounded model W m k Qv a c hc digits hd trees hv hp count innerCount rowCount tailCount hcount hi hr ht j i q r learner)
    (GeneralPaperFieldFamilyConstructionStorage.row_bounded model W a _ _ _
      (GeneralPaperEpochCacheConstructionStorage.inputs_valid model W _ a _ _ (valid_four model W m k Qv a c hc digits trees hv hp)) j)

end Blotto.GeneralPaperTreeEpochConstructionStorage
