import Blotto.GeneralPaperNativeEndpointSourceJoin

/-! Stored circle preparation agrees across all primitive/index models.
Only price observers differ; the actual sort, coefficients and metadata
are identical. No data-path height or capacity query is used. -/
namespace Blotto.GeneralPaperPreparedCircleModels
set_option autoImplicit false
set_option maxHeartbeats 2200000

theorem metadata {g : ℕ} (price price' : ℕ → ℕ) (A A' R : ℕ) (weights : FixedArrayTable g ℕ) :
    (GeneralPaperNativeChoiceArray.prepare price A R weights).1=
      (GeneralPaperNativeChoiceArray.prepare price' A' R weights).1 := by
  unfold GeneralPaperNativeChoiceArray.prepare
  dsimp only
  congr 1
  exact congrArg GeneralPaperCircleArcMetadata.Result.arcs
    (GeneralPaperCircleArcMetadata.models_data price price' A A' R (List.ofFn weights.read) 0)

theorem data {n R : ℕ} (price price' index index' : ℕ → ℕ) (A A' W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (row : FixedArrayTable R ℚ) (weights : FixedArrayTable state.light.size ℕ) :
    (GeneralPaperNamedCircleExecution.prepare price index A W state kept row weights).1=
      (GeneralPaperNamedCircleExecution.prepare price' index' A' W state kept row weights).1 := by
  dsimp only [GeneralPaperNamedCircleExecution.prepare]
  rw [GeneralPaperNativeSortedRows.one_data,GeneralPaperNativeSortedRows.one_data,
    GeneralPaperCircleRationalCoefficients.data,GeneralPaperCircleRationalCoefficients.data,metadata price price' A A' R weights]

end Blotto.GeneralPaperPreparedCircleModels
