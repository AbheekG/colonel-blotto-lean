import Blotto.GeneralPaperRoundExecution

/-! The reached round joins each existing component once. Snapshot and
row equalities identify retained objects in the cost proof; they do not
execute another query, selector, code pass or field update. -/
namespace Blotto.GeneralPaperRoundPrice
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def profile (model : RationalCostModel) (W m lambda k Qv J height leaves BcWord BrWord : ℕ) : ℕ :=
  GeneralPaperEpochSnapshotFamilyPrice.profile model.rat W m lambda k Qv+
    GeneralPaperChooseRowsPrice.profile model W m lambda k Qv J height leaves BcWord BrWord+
    GeneralPaperRoundFieldsPrice.profile model.rat W m lambda k Qv+
    2*GeneralPaperSelectedRowCodesPrice.profile W m ((GeneralPaperSourceParameters.prepare k).summarySize+2) lambda+256*W

def arithmeticProfile (m lambda k Qv J depth height leaves : ℕ) : ℕ :=
  GeneralPaperEpochSnapshotFamilyPrice.arithmeticProfile m lambda k Qv+
    GeneralPaperChooseRowsPrice.arithmeticProfile m k J depth height leaves+
    GeneralPaperRoundFieldsPrice.arithmeticProfile m k+2*(173*m+108)+256

theorem sum_five (s r u c d S R U C W : ℕ) (hs : s≤S) (hr : r≤R) (hu : u≤U) (hc : c≤C) (hd : d≤C) :
    s+r+u+c+d+256*W≤S+R+U+2*C+256*W := by omega

theorem work {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (hCodes : GeneralPaperCatalogueEpochMetadata.CodesValid cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hWeights : ∑ j,weights.read j=Qv) (time : ℕ) (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    let current := selected cache Qv weights Bc Br
    (GeneralPaperRoundExecution.run true (fun x => x) model.rat W c cache current.profit current.T weights Bc Br (stateAt current time)).2≤
      profile model W m cache.alphabet.lambda k Qv current.profit.grid.size current.profit.parameters.height current.profit.parameters.leafCount (rationalWordWidth Bc) (rationalWordWidth Br) ∧
    (GeneralPaperRoundExecution.run false (fun _ => 1) model.rat 1 c cache current.profit current.T weights Bc Br (stateAt current time)).2≤
      arithmeticProfile m cache.alphabet.lambda k Qv current.profit.grid.size current.profit.grid.depth current.profit.parameters.height current.profit.parameters.leafCount := by
  let current := selected cache Qv weights Bc Br
  have hSpan : current.profit.parameters.leafCount=2^current.profit.parameters.height := GeneralPaperProfitParameters.leaf_count_spec m cache.alphabet.lambda k Qv
  have hs := GeneralPaperActualEpochSnapshotPrice.selected_work model W Qv cache c hc weights Bc Br time ht
  have hr := GeneralPaperChooseRowsPrice.selected_work model W Qv cache weights Bc Br hWeights time ht
  have hu := GeneralPaperRoundFieldsPrice.work model W Qv cache c hc hCodes weights Bc Br time ht
  have hca : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  have hra : cache.response.alphabet=cache.alphabet := by rw [cache.response_spec]; rfl
  have hcb := GeneralPaperSelectedRowCodesPrice.work W cache.candidate (rowsAt current time).candidate
  have hrb := GeneralPaperSelectedRowCodesPrice.work W cache.response (rowsAt current time).response
  rw [hca] at hcb
  rw [hra] at hrb
  have hcu := GeneralPaperSelectedRowCodesPrice.arithmetic_work cache.candidate.data (rowsAt current time).candidate
  have hru := GeneralPaperSelectedRowCodesPrice.arithmetic_work cache.response.data (rowsAt current time).response
  have hsb := GeneralPaperActualEpochSnapshotPrice.selected_data true (fun x => x) model.rat W Qv cache c hc weights Bc Br time
  have hsu := GeneralPaperActualEpochSnapshotPrice.selected_data false (fun _ => 1) model.rat 1 Qv cache c hc weights Bc Br time
  have hrdb : (GeneralPaperChooseRowsExecution.run true (fun x => x) model.rat W cache current.profit current.T weights (beforeAt current time) Bc Br).1=rowsAt current time :=
    GeneralPaperChooseRowsExecution.data true (fun x => x) model.rat W cache current.profit current.T weights _ Bc Br hSpan
  have hrdu : (GeneralPaperChooseRowsExecution.run false (fun _ => 1) model.rat 1 cache current.profit current.T weights (beforeAt current time) Bc Br).1=rowsAt current time :=
    GeneralPaperChooseRowsExecution.data false (fun _ => 1) model.rat 1 cache current.profit current.T weights _ Bc Br hSpan
  constructor
  · have h := sum_five _ _ _ _ _ _ _ _ _ W hs.1 hr.1 hu.1 hcb hrb
    rw [←hrdb,←hsb] at h
    exact h
  · have h := sum_five _ _ _ _ _ _ _ _ _ 1 hs.2 hr.2 hu.2 hcu hru
    rw [←hrdu,←hsu] at h
    exact h

theorem data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ) :
    let current := selected cache Qv weights Bc Br
    (GeneralPaperRoundExecution.run bits index price W c cache current.profit current.T weights Bc Br (stateAt current time)).1=
      GeneralPaperCatalogueEpoch.round cache current.powers current.profit current.T weights Bc Br (stateAt current time) := by
  dsimp only
  rw [GeneralPaperRoundExecution.data bits index price W cache.alphabet.lambda Qv c hc]
  · rw [hc]
    rfl
  · exact GeneralPaperProfitParameters.leaf_count_spec m cache.alphabet.lambda k Qv

theorem next_state {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ) :
    let current := selected cache Qv weights Bc Br
    (GeneralPaperRoundExecution.run bits index price W c cache current.profit current.T weights Bc Br (stateAt current time)).1.state=stateAt current (time+1) := by
  dsimp only
  rw [data bits index price W Qv cache c hc]
  rfl

end Blotto.GeneralPaperRoundPrice
