import Blotto.GeneralPaperLocalEpochLoopPrice

/-! The priced loop visits the selected native states, and records exactly
the same pre-update candidate trajectory. These observers do not rerun it. -/
namespace Blotto.GeneralPaperSelectedLocalEpochExecution
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem prefix_state {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (capacity time : ℕ) :
    let current := selected cache Qv weights Bc Br
    (GeneralPaperLocalEpochExecution.run bits index price W c cache current.profit current.T weights Bc Br
      (GeneralPaperEpochInitialFamilyPrice.run bits index (if bits then price else fun _ => 1) W cache).1 capacity time).1.1=
        stateAt current time := by
  dsimp only
  rw [GeneralPaperLocalEpochExecution.data bits index price W cache.alphabet.lambda Qv c hc]
  · rw [GeneralPaperEpochInitialFamilyPrice.data,hc]
    rfl
  · exact GeneralPaperProfitParameters.leaf_count_spec m cache.alphabet.lambda k Qv

theorem data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (capacity count : ℕ) :
    let current := selected cache Qv weights Bc Br
    (GeneralPaperLocalEpochExecution.execute bits index price W c cache current.profit current.T weights Bc Br capacity count).1=
      GeneralPaperCatalogueEpoch.execute cache current.powers current.profit current.T weights Bc Br (initial cache) count := by
  dsimp only
  rw [GeneralPaperLocalEpochExecution.execute_data bits index price W cache.alphabet.lambda Qv c hc]
  · rw [hc]
    rfl
  · exact GeneralPaperProfitParameters.leaf_count_spec m cache.alphabet.lambda k Qv

theorem recorded_row {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (capacity count time : ℕ) (ht : time<count) :
    let current := selected cache Qv weights Bc Br
    let rows := (GeneralPaperLocalEpochExecution.execute bits index price W c cache current.profit current.T weights Bc Br capacity count).1.2
    ∃ h : time<rows.size, rows[time]'h=
      (GeneralPaperCatalogueEpoch.round cache current.powers current.profit current.T weights Bc Br (stateAt current time)).candidate := by
  dsimp only
  rw [data bits index price W Qv cache c hc]
  exact ⟨by rw [GeneralPaperCatalogueEpoch.trajectory_size]; exact ht,
    GeneralPaperCatalogueEpoch.trajectory_read _ _ _ _ _ _ _ _ count time ht⟩

end Blotto.GeneralPaperSelectedLocalEpochExecution
