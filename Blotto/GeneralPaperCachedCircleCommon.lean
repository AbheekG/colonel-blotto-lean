import Blotto.GeneralPaperOriginalValueBitDriverRate

/-! One retained original-light-field cache for all circle rows and both
players. Weights, rational coefficients and choice metadata are shared;
row construction never runs either light-field constructor again. -/
namespace Blotto.GeneralPaperCachedCircleCommon
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

structure Cache (g : ℕ) where
  weights : FixedArrayTable g ℕ
  coefficients : FixedArrayTable g ℚ
  metadata : GeneralPaperNativeChoiceArray.Prepared g

def run {g : ℕ} (price index : ℕ → ℕ) (A R W : ℕ) (weights : FixedArrayTable g ℕ) : Cache g×ℕ :=
  let coefficients := GeneralPaperCircleRationalCoefficients.run price index A R W weights
  let metadata := GeneralPaperNativeChoiceArray.prepare price A R weights
  (⟨weights,coefficients.1,metadata.1⟩,coefficients.2+metadata.2+64*A)

def view {n R : ℕ} (state : GeneralPaperLightFieldScan.State n) (common : Cache state.light.size)
    (kept : FixedArrayTable state.heavy.size ℚ) (sorted : FixedArrayTable R ℚ) : GeneralPaperNamedCircleExecution.Prepared state R :=
  ⟨kept,sorted,common.coefficients,common.metadata⟩

theorem weights_data {g : ℕ} (price index : ℕ → ℕ) (A R W : ℕ) (weights : FixedArrayTable g ℕ) :
    (run price index A R W weights).1.weights=weights := rfl

theorem coefficients_data {g : ℕ} (price index : ℕ → ℕ) (A R W : ℕ) (weights : FixedArrayTable g ℕ) :
    (run price index A R W weights).1.coefficients=
      FixedArrayTable.ofFn (fun j => ((R*weights.read j:ℕ):ℚ)/W) :=
  GeneralPaperCircleRationalCoefficients.data price index A R W weights

theorem metadata_data {g : ℕ} (price index : ℕ → ℕ) (A R W : ℕ) (weights : FixedArrayTable g ℕ) :
    (run price index A R W weights).1.metadata=(GeneralPaperNativeChoiceArray.prepare price A R weights).1 := rfl

theorem models_data {g : ℕ} (price price' index index' : ℕ → ℕ) (A A' R W : ℕ) (weights : FixedArrayTable g ℕ) :
    (run price index A R W weights).1=(run price' index' A' R W weights).1 := by
  dsimp only [run]
  rw [GeneralPaperCircleRationalCoefficients.data,GeneralPaperCircleRationalCoefficients.data,
    GeneralPaperPreparedCircleModels.metadata price price' A A' R weights]

theorem prepared_view {n R : ℕ} (price index : ℕ → ℕ) (A W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (weights : FixedArrayTable state.light.size ℕ) (kept : FixedArrayTable state.heavy.size ℚ) (row : FixedArrayTable R ℚ) :
    view state (run price index A R W weights).1 kept (GeneralPaperNativeSortedRows.one price index A row).1=
      (GeneralPaperNamedCircleExecution.prepare price index A W state kept row weights).1 := rfl

def fromOriginal {n : ℕ} (price index : ℕ → ℕ) (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : Cache o.classified.light.size×ℕ :=
  let weights := GeneralPaperNativeLightWeights.run index A o
  let common := run price index A o.representatives o.classified.lightWeight weights.1
  (common.1,weights.2+common.2+64*A)

theorem original_data {n : ℕ} (price index : ℕ → ℕ) (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    (fromOriginal price index A o).1=
      (run price index A o.representatives o.classified.lightWeight (GeneralPaperNativeLightWeights.run index A o).1).1 := rfl

theorem original_weights {n : ℕ} (price index : ℕ → ℕ) (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    (fromOriginal price index A o).1.weights=FixedArrayTable.ofFn (GeneralPaperCircleActualWeights.weights o) :=
  GeneralPaperNativeLightWeights.data index A o

theorem original_models {n : ℕ} (price price' index index' : ℕ → ℕ) (A A' : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    (fromOriginal price index A o).1=(fromOriginal price' index' A' o).1 := by
  dsimp only [fromOriginal]
  rw [GeneralPaperNativeLightWeights.models_data index index' A A' o,models_data price price' index index' A A' _ _]

end Blotto.GeneralPaperCachedCircleCommon
