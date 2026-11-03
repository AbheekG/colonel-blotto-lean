import Blotto.GeneralPaperActualNativeSelectorPrice
import Blotto.GeneralPaperRoundPrefixViews

/-! Both complete selectors borrow one pair of signed-prefix views from the
same retained snapshot. Row records contain the returned native indices. -/
namespace Blotto.GeneralPaperChooseRowsExecution
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRows
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (cache : Cache m k)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (before : FixedArrayTable m (GeneralPaperEpochSnapshot.Snapshot k)) (Bc Br : ℚ) : Rows m k × ℕ :=
  let views := GeneralPaperRoundPrefixViews.run bits index W before
  let candidate := GeneralPaperNativeSelectorExecution.pick bits index price W profit T cache.candidate weights views.1.1 Bc
  let response := GeneralPaperNativeSelectorExecution.pick bits index price W profit T cache.response weights views.1.2 Br
  (⟨candidate.1,response.1⟩,views.2+candidate.2+response.2+128*W)

theorem data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (cache : Cache m k)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (before : FixedArrayTable m (GeneralPaperEpochSnapshot.Snapshot k)) (Bc Br : ℚ)
    (hSpan : profit.parameters.leafCount=2^profit.parameters.height) :
    (run bits index price W cache profit T weights before Bc Br).1=chooseRows cache profit T weights before Bc Br := by
  simp only [run,GeneralPaperRoundPrefixViews.data,
    GeneralPaperNativeSelectorExecution.pick_data bits index price W profit T cache.candidate weights _ Bc hSpan,
    GeneralPaperNativeSelectorExecution.pick_data bits index price W profit T cache.response weights _ Br hSpan,chooseRows]

end Blotto.GeneralPaperChooseRowsExecution
