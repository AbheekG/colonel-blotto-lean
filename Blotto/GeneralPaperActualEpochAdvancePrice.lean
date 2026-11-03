import Blotto.GeneralPaperEpochFieldAdvancePrice
import Blotto.GeneralPaperActualEpochSnapshotPrice

/-! Reached local states and their one shared snapshot derive every input
and delta cap. All eight priced additions return the actual next native field
and its retained plan. No field, selector or delta is replayed by these joins.
-/
namespace Blotto.GeneralPaperActualEpochAdvancePrice
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem delta_bounded {m k : ℕ} (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    (deltaAt (selected cache Qv weights Bc Br) time j).Bounded
      (8*(GeneralPaperSourceParameters.prepare k).meshDenominator) :=
  GeneralPaperEpochDeltas.generated_bound _ _ _
    (GeneralPaperCatalogueEpochRun.selected_positive cache Qv weights Bc Br time ht j)
    (snapshot_coherent (selected cache Qv weights Bc Br) time j)

theorem data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ) (j : Fin m) :
    let current := selected cache Qv weights Bc Br
    (GeneralPaperEpochFieldAdvancePrice.run bits index price W (fieldAt current time j) (deltaAt current time j)).1=
      fieldAt current (time+1) j := by
  dsimp only
  rw [GeneralPaperEpochFieldAdvancePrice.data]
  exact (field_step (selected cache Qv weights Bc Br) time j).symm

theorem work {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : Cache m k)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    let current := selected cache Qv weights Bc Br
    let field := fieldAt current time j
    let delta := deltaAt current time j
    (GeneralPaperEpochFieldAdvancePrice.run true (fun w => w) model.rat W field delta).2≤
      GeneralPaperEpochFieldAdvancePrice.profile model.rat W m cache.alphabet.lambda Qv field ∧
    (GeneralPaperEpochFieldAdvancePrice.run false (fun _ => 1) (fun _ => 1) 1 field delta).2≤
      GeneralPaperEpochFieldAdvancePrice.arithmeticProfile field := by
  exact ⟨GeneralPaperEpochFieldAdvancePrice.bit_work model.rat model.monotone W m cache.alphabet.lambda Qv _ _
      (selected_cap cache Qv weights Bc Br time ht j) (delta_bounded cache Qv weights Bc Br time ht j),
    GeneralPaperEpochFieldAdvancePrice.arithmetic_work _ _⟩

theorem returned_cap {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    let current := selected cache Qv weights Bc Br
    GeneralPaperEpochFieldState.Bounded
      (GeneralPaperEpochFieldAdvancePrice.run bits index price W (fieldAt current time j) (deltaAt current time j)).1
        (GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) := by
  dsimp only
  rw [data]
  exact selected_cap cache Qv weights Bc Br (time+1) ht j

theorem returned_plan {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ) (j : Fin m) :
    let current := selected cache Qv weights Bc Br
    (GeneralPaperEpochFieldAdvancePrice.run bits index price W (fieldAt current time j) (deltaAt current time j)).1.plan=
      cache.plans.read j := by
  dsimp only
  rw [GeneralPaperEpochFieldAdvancePrice.retained_plan]
  exact field_plan _ time j

theorem same_data {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : Cache m k)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ) (j : Fin m) :
    let current := selected cache Qv weights Bc Br
    (GeneralPaperEpochFieldAdvancePrice.run true (fun w => w) model.rat W (fieldAt current time j) (deltaAt current time j)).1=
      (GeneralPaperEpochFieldAdvancePrice.run false (fun _ => 1) (fun _ => 1) 1 (fieldAt current time j) (deltaAt current time j)).1 := by
  dsimp only
  rw [data true (fun w => w) model.rat W Qv cache,data false (fun _ => 1) (fun _ => 1) 1 Qv cache]

end Blotto.GeneralPaperActualEpochAdvancePrice
