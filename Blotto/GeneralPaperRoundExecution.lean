import Blotto.GeneralPaperSelectedRowCodesPrice

/-! One common snapshot, two complete native selectors, one all-field
update and the two selected code arrays. The returned candidate is the
pre-update choice used by exactly these eight-array field updates. -/
namespace Blotto.GeneralPaperRoundExecution
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRows
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def run {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (state : State cache) :
    GeneralPaperCatalogueEpoch.RoundResult cache × ℕ :=
  let before := GeneralPaperEpochSnapshotFamilyPrice.run bits index price W c state.fields
  let rows := GeneralPaperChooseRowsExecution.run bits index price W cache profit T weights before.1 Bc Br
  let updated := GeneralPaperRoundFieldsExecution.run bits index price W c.controls.source.meshDenominator state before.1 rows.1
  let candidate := GeneralPaperSelectedRowCodesPrice.run bits index W cache.candidate.data rows.1.candidate
  let response := GeneralPaperSelectedRowCodesPrice.run bits index W cache.response.data rows.1.response
  (⟨updated.1,candidate.1,response.1⟩,before.2+rows.2+updated.2+candidate.2+response.2+256*W)

theorem data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (Bc Br : ℚ) (state : State cache) (hSpan : profit.parameters.leafCount=2^profit.parameters.height) :
    (run bits index price W c cache profit T weights Bc Br state).1=
      GeneralPaperCatalogueEpoch.round cache c.powers profit T weights Bc Br state := by
  have hMesh : c.controls.source.meshDenominator=(GeneralPaperSourceParameters.prepare k).meshDenominator := by rw [hc]; rfl
  unfold run
  dsimp only
  rw [GeneralPaperEpochSnapshotFamilyPrice.data bits index price W lambda Qv c hc,
    GeneralPaperChooseRowsExecution.data bits index price W cache profit T weights _ Bc Br hSpan,
    GeneralPaperSelectedRowCodesPrice.data,GeneralPaperSelectedRowCodesPrice.data,
    GeneralPaperRoundFieldsExecution.round_data bits index price W _ cache c.powers profit T weights Bc Br state hMesh]
  rfl

end Blotto.GeneralPaperRoundExecution
