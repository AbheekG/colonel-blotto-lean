import Blotto.GeneralPaperFieldFamilyActiveStorage

/-! Native epoch-cache construction joins both actual Ready objects, the
eight-plan field-family buffers, the complete returned cache and primitive
scratch. Native Ready data supplies option-code premises without replay. -/
namespace Blotto.GeneralPaperEpochCacheConstructionStorage
open GeneralPaperCodeAlphabet GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def ValidFour {m k : ℕ} (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k) : Prop :=
  (∀ j i,(arrays.p.read j).read i<8*a.C) ∧ (∀ j i,(arrays.q.read j).read i<8*a.C) ∧
  (∀ j i,(arrays.lambda.read j).read i<2*(8*a.C)) ∧ (∀ j i,(arrays.mu.read j).read i<2*(8*a.C))

def candidate {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :=
  (GeneralPaperCatalogueOptimizerPreparation.run true (fun w => w) model W k mesh a false arrays.lambda hm).1

def response {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :=
  (GeneralPaperCatalogueOptimizerPreparation.run true (fun w => w) model W k mesh a true arrays.mu hm).1

theorem inputs_valid {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hv : ValidFour a arrays) :
    GeneralPaperFieldFamilyConstructionStorage.ValidInputs a arrays
      (candidate model W mesh a arrays hm).data.codes (response model W mesh a arrays hm).data.codes := by
  rcases hv with ⟨hp,hq,hl,hu⟩
  refine ⟨hp,hq,hl,hu,?_,?_⟩
  · intro j i
    unfold candidate
    rw [GeneralPaperCatalogueOptimizerPreparation.data]
    exact GeneralPaperCatalogueArrays.code_bound a false k arrays.lambda j i
  · intro j i
    unfold response
    rw [GeneralPaperCatalogueOptimizerPreparation.data]
    exact GeneralPaperCatalogueArrays.code_bound a true k arrays.mu j i

theorem returned {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hv : ValidFour a arrays) :
    GeneralPaperEncodedEpochCache.footprint W (GeneralPaperEpochCachePreparation.run true (fun w => w) model W k mesh a arrays hm).1≤
      GeneralPaperEncodedEpochCache.profile W m a.lambda k := by
  have hvalid : GeneralPaperCatalogueEpochMetadata.CodesValid
      (GeneralPaperEpochCachePreparation.run true (fun w => w) model W k mesh a arrays hm).1 := by
    rw [GeneralPaperEpochCachePreparation.data]
    intro learner j i
    cases learner
    · exact hv.1 j i
    · exact hv.2.1 j i
    · exact hv.2.2.1 j i
    · exact hv.2.2.2 j i
  exact GeneralPaperEncodedEpochCache.bounded W _ hvalid

def window {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (count rowCount tailCount : ℕ) (hc : count≤m) (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) : ℕ :=
  GeneralPaperReadyConstructionStorage.window model W mesh a false arrays.lambda hm count rowCount tailCount hc hr ht j i q+
    GeneralPaperReadyConstructionStorage.window model W mesh a true arrays.mu hm count rowCount tailCount hc hr ht j i q+
    GeneralPaperFieldFamilyConstructionStorage.window model W a arrays
      (candidate model W mesh a arrays hm).data.codes (response model W mesh a arrays hm).data.codes count hc+
    GeneralPaperEncodedEpochCache.footprint W (GeneralPaperEpochCachePreparation.run true (fun w => w) model W k mesh a arrays hm).1+
    fields W [8,a.C,8*a.C,k,mesh,m]+(GeneralPaperEpochCachePreparation.run true (fun w => w) model W k mesh a arrays hm).2+256*W

def profile (model : RationalCostModel) (W m k mesh : ℕ) (a : Alphabet) : ℕ :=
  2*GeneralPaperReadyConstructionStorage.profile model W m k mesh a+GeneralPaperFieldFamilyConstructionStorage.profile model W m k a+
    GeneralPaperEncodedEpochCache.profile W m a.lambda k+fields W [8,a.C,8*a.C,k,mesh,m]+
    GeneralPaperEpochCachePreparation.profile model W m k a+256*W

theorem bounded {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hv : ValidFour a arrays)
    (count rowCount tailCount : ℕ) (hc : count≤m) (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) :
    window model W mesh a arrays hm count rowCount tailCount hc hr ht j i q≤profile model W m k mesh a := by
  have hca := GeneralPaperReadyConstructionStorage.bounded model W mesh a false arrays.lambda hm hv.2.2.1 count rowCount tailCount hc hr ht j i q
  have hra := GeneralPaperReadyConstructionStorage.bounded model W mesh a true arrays.mu hm hv.2.2.2 count rowCount tailCount hc hr ht j i q
  have hf := GeneralPaperFieldFamilyConstructionStorage.bounded model W a arrays
    (candidate model W mesh a arrays hm).data.codes (response model W mesh a arrays hm).data.codes
    (inputs_valid model W mesh a arrays hm hv) count hc
  have hout := returned model W mesh a arrays hm hv
  have hp := GeneralPaperEpochCachePreparation.bit_work model W k mesh a arrays hm hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
  unfold window profile
  omega

theorem with_field_context {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hv : ValidFour a arrays)
    (count rowCount tailCount : ℕ) (hc : count≤m) (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) :
    window model W mesh a arrays hm count rowCount tailCount hc hr ht j i q+
      GeneralPaperFieldFamilyConstructionStorage.rowWindow model W a arrays
        (candidate model W mesh a arrays hm).data.codes (response model W mesh a arrays hm).data.codes j≤
      profile model W m k mesh a+GeneralPaperFieldFamilyConstructionStorage.rowProfile model W k a :=
  Nat.add_le_add (bounded model W mesh a arrays hm hv count rowCount tailCount hc hr ht j i q)
    (GeneralPaperFieldFamilyConstructionStorage.row_bounded model W a arrays
      (candidate model W mesh a arrays hm).data.codes (response model W mesh a arrays hm).data.codes (inputs_valid model W mesh a arrays hm hv) j)

theorem with_occurrence_children {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hv : ValidFour a arrays)
    (count rowCount tailCount : ℕ) (hc : count≤m) (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q0 : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) (mode : Bool)
    (cdfCount occurrenceTail signedCount : ℕ) (hCDF : cdfCount≤(GeneralPaperSourceParameters.prepare k).summarySize)
    (hTail : occurrenceTail≤(GeneralPaperSourceParameters.prepare k).summarySize+1)
    (hSigned : signedCount≤(GeneralPaperSourceParameters.prepare k).summarySize) (q : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1)) :
    let ca := (candidate model W mesh a arrays hm).data.codes
    let re := (response model W mesh a arrays hm).data.codes
    window model W mesh a arrays hm count rowCount tailCount hc hr ht j i q0+
      (GeneralPaperFieldFamilyConstructionStorage.window model W a arrays ca re count hc+
        GeneralPaperFieldFamilyConstructionStorage.rowWindow model W a arrays ca re j+
        GeneralPaperQueryLossConstructionStorage.window model W k (8*a.C) (GeneralPaperFieldFamilyActiveStorage.opposite arrays mode j)
          (GeneralPaperFieldFamilyActiveStorage.signed arrays mode j) (GeneralPaperFieldFamilyActiveStorage.own arrays mode j) cdfCount occurrenceTail hCDF hTail q+
        GeneralPaperSignedUpdateConstructionStorage.window model W k (8*a.C) (GeneralPaperFieldFamilyActiveStorage.own arrays mode j)
          (GeneralPaperFieldFamilyActiveStorage.signed arrays mode j) signedCount hSigned)≤
      profile model W m k mesh a+(GeneralPaperFieldFamilyConstructionStorage.profile model W m k a+
        GeneralPaperFieldFamilyConstructionStorage.rowProfile model W k a+
        GeneralPaperQueryLossConstructionStorage.profile model W (GeneralPaperSourceParameters.prepare k).summarySize k (8*a.C)+
        GeneralPaperSignedUpdateConstructionStorage.profile model W (GeneralPaperSourceParameters.prepare k).summarySize k (8*a.C)) :=
  Nat.add_le_add (bounded model W mesh a arrays hm hv count rowCount tailCount hc hr ht j i q0)
    (GeneralPaperFieldFamilyActiveStorage.with_occurrence_children model W a arrays
      (candidate model W mesh a arrays hm).data.codes (response model W mesh a arrays hm).data.codes
      (inputs_valid model W mesh a arrays hm hv) count hc mode j cdfCount occurrenceTail signedCount hCDF hTail hSigned q)

theorem with_cell_children {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hv : ValidFour a arrays)
    (count rowCount tailCount : ℕ) (hc : count≤m) (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q0 : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) (mode : Bool) :
    let ca := (candidate model W mesh a arrays hm).data.codes
    let re := (response model W mesh a arrays hm).data.codes
    let own := GeneralPaperFieldFamilyActiveStorage.own arrays mode j
    let other := GeneralPaperFieldFamilyActiveStorage.opposite arrays mode j
    let signed := GeneralPaperFieldFamilyActiveStorage.signed arrays mode j
    let bids := GeneralPaperFieldFamilyActiveStorage.options ca re mode j
    let U := 8*a.C
    let s := (GeneralPaperSourceParameters.prepare k).summarySize
    let K := s+2
    let u := GeneralPaperCellPlanConstructionStorage.unsignedPart model W k U other signed bids
    let t := GeneralPaperCellPlanConstructionStorage.signedPart model W k U own bids
    ∀ inputCount positionCount extraCount usedP usedE copied cellCountU cellCountS repCountU repCountS cdfCount occurrenceTail rankCount
      (hi : inputCount≤s+K) (hp : positionCount≤2*s) (he : extraCount≤2*K+1)
      (hcu : cellCountU≤u.count) (hcs : cellCountS≤t.count) (hru : repCountU≤u.count) (hrs : repCountS≤t.count)
      (hCDF : cdfCount≤u.count) (hTail : occurrenceTail≤u.count+1) (hq : rankCount≤t.count) (q : Fin (u.count+1)),
    window model W mesh a arrays hm count rowCount tailCount hc hr ht j i q0+
      (GeneralPaperFieldFamilyConstructionStorage.window model W a arrays ca re count hc+
        GeneralPaperFieldFamilyConstructionStorage.rowWindow model W a arrays ca re j+
        GeneralPaperCellPlanConstructionStorage.unsignedWindow model W k U other signed bids
          inputCount usedP usedE copied cellCountU repCountU cdfCount occurrenceTail hi hcu hru hCDF hTail q+
        GeneralPaperCellPlanConstructionStorage.signedWindow model W k U own bids
          positionCount extraCount usedP usedE copied cellCountS repCountS rankCount hp he hcs hrs hq)≤
      profile model W m k mesh a+(GeneralPaperFieldFamilyConstructionStorage.profile model W m k a+
        GeneralPaperFieldFamilyConstructionStorage.rowProfile model W k a+
        GeneralPaperCellPlanConstructionStorage.unsignedProfile model W k U K+GeneralPaperCellPlanConstructionStorage.signedProfile model W k U K) := by
  have hb := bounded model W mesh a arrays hm hv count rowCount tailCount hc hr ht j i q0
  have hf := GeneralPaperFieldFamilyActiveStorage.with_cell_children model W a arrays
    (candidate model W mesh a arrays hm).data.codes (response model W mesh a arrays hm).data.codes
    (inputs_valid model W mesh a arrays hm hv) count hc mode j
  dsimp only at hf ⊢
  intro inputCount positionCount extraCount usedP usedE copied cellCountU cellCountS repCountU repCountS cdfCount occurrenceTail rankCount
    hi hp he hcu hcs hru hrs hCDF hTail hq q
  exact Nat.add_le_add hb (hf inputCount positionCount extraCount usedP usedE copied cellCountU cellCountS repCountU repCountS cdfCount occurrenceTail rankCount
    hi hp he hcu hcs hru hrs hCDF hTail hq q)

theorem with_ready_catalogue_child {m k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (a : Alphabet) (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hv : ValidFour a arrays)
    (count rowCount tailCount : ℕ) (hc : count≤m) (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (ht : tailCount≤((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (q0 : Fin (((GeneralPaperSourceParameters.prepare k).summarySize+2)+1)) (mode : Bool) (field : GeneralPaperCatalogueProjection.Field) :
    let summaries := if mode then arrays.mu else arrays.lambda
    ∀ copied used rowCopied partCount rawCount padCount (hcopied : copied≤m)
      (hp : partCount≤(GeneralPaperCachedCatalogueStorage.part a (summaries.read j)).count)
      (hraw : rawCount≤(GeneralPaperCachedCatalogueStorage.part a (summaries.read j)).count)
      (hpad : padCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2),
    window model W mesh a arrays hm count rowCount tailCount hc hr ht j i q0+
      (GeneralPaperCatalogueArrayConstructionStorage.window model W a mode summaries field count copied rowCount hc hcopied hr j+
        GeneralPaperCachedCatalogueStorage.window model W a mode (summaries.read j) used rowCopied partCount rawCount padCount hp hraw hpad)≤
      profile model W m k mesh a+(GeneralPaperCatalogueArrayConstructionStorage.profile model W m
        (GeneralPaperSourceParameters.prepare k).summarySize a+GeneralPaperCachedCatalogueStorage.profile model W
          (GeneralPaperSourceParameters.prepare k).summarySize a) := by
  have hb := bounded model W mesh a arrays hm hv count rowCount tailCount hc hr ht j i q0
  have hs : ∀ j i,((if mode then arrays.mu else arrays.lambda).read j).read i<2*(8*a.C) := by
    cases mode
    · exact hv.2.2.1
    · exact hv.2.2.2
  dsimp only
  intro copied used rowCopied partCount rawCount padCount hcopied hp hraw hpad
  exact Nat.add_le_add hb (GeneralPaperCatalogueArrayConstructionStorage.with_cached_constructor model W a mode _ hs field
    count copied rowCount hc hcopied hr j used rowCopied partCount rawCount padCount hp hraw hpad)

end Blotto.GeneralPaperEpochCacheConstructionStorage
