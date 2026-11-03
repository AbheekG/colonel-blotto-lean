import Blotto.GeneralPaperRetainedFieldValues

/-! One full matrix, one full lower-score DP, one strict budget scan and
one stored-matrix maximum. All consume retained physical columns and a
stored normalized value array; the matrix is returned for the basis and
both final checks. No source/quantizer/value/matrix replay occurs here. -/
namespace Blotto.GeneralPaperRetainedTransferPreparation
open GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperComputedThreshold
open GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 2600000

structure Output (T m K S : ℕ) where
  prepared : GeneralPaperTransferPreparation.Prepared T m K S
  matrix : FixedArrayTable m (Field K)
  maximum : ℕ
  budget : ℚ

def dp {K : ℕ} (bits : Bool) (model : RationalCostModel) (W S : ℕ) (fields : List (Field K)) :
    FixedArrayTable (S+1) (Option (Selection K))×ℕ :=
  if bits then GeneralPaperScoreDPBits.runWithBits model W S fields else GeneralPaperScoreDPWork.runWithWork S fields

theorem dp_data {K : ℕ} (bits : Bool) (model : RationalCostModel) (W S : ℕ) (fields : List (Field K)) :
    (dp bits model W S fields).1=GeneralPaperExactScoreDP.run S fields := by
  cases bits with
  | false => exact GeneralPaperScoreDPWork.run_data S fields
  | true => exact GeneralPaperScoreDPBits.run_data model W S fields

def threshold {K S : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) : ℕ×ℕ :=
  if bits then GeneralPaperThresholdScanBits.runWithBits model W table budget else GeneralPaperThresholdScanWork.run table budget

theorem threshold_data {K S : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (table : FixedArrayTable (S+1) (Option (Selection K))) (budget : ℚ) :
    (threshold bits model W table budget).1=scanThreshold table budget := by
  cases bits with
  | false => exact GeneralPaperThresholdScanWork.run_data table budget
  | true => exact GeneralPaperThresholdScanBits.run_data model W table budget

def run {T m K : ℕ} (bits : Bool) (model : RationalCostModel) (W depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (values : GeneralPaperRetainedFieldValues.Values m)
    (ownBudget opposingProxy : ℚ) : Output T m K S×ℕ :=
  let v := GeneralPaperRetainedFieldValues.selector values
  let matrix := GeneralPaperPhysicalScoreMatrix.run bits model W depth columns v S
  let fields := matrix.1.data.toList
  let table := dp bits model W S fields
  let budget := opposingProxy/ownBudget
  let selected := threshold bits model W table.1 budget
  let maximum := GeneralPaperStoredScoreMaximum.run bits model W hK matrix.1
  (⟨⟨GeneralPaperRowQuantizer.dictionary columns,table.1,selected.1⟩,matrix.1,maximum.1,budget⟩,
    matrix.2+table.2+selected.2+maximum.2+GeneralPaperRationalPrimitivePrice.binary (primitive bits model) (fun a b => a/b)
      opposingProxy ownBudget+64*(m+1)*address bits W (m+K+S)+64*address bits W (m+K+S))

theorem fields_data {T m K : ℕ} (bits : Bool) (model : RationalCostModel) (W depth S : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (v : RationalFieldSelector m)
    (hK : 0<K) (hCap : S<2^depth) :
    (GeneralPaperPhysicalScoreMatrix.run bits model W depth columns v S).1.data.toList=
      GeneralPaperExactScoreDP.fields (GeneralPaperStrictScore.score v S) (GeneralPaperRowQuantizer.dictionary columns).anchor := by
  rw [GeneralPaperPhysicalScoreMatrix.data bits model W depth columns v S hK hCap]
  simp only [FixedArrayTable.ofFn,Array.toList_ofFn,GeneralPaperExactScoreDP.fields,GeneralPaperRowQuantizer.dictionary]

theorem data {T m K : ℕ} (bits : Bool) (model : RationalCostModel) (W depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (values : GeneralPaperRetainedFieldValues.Values m)
    (ownBudget opposingProxy : ℚ) (hCap : S<2^depth) :
    (run bits model W depth S hK columns values ownBudget opposingProxy).1.prepared=
      (⟨GeneralPaperRowQuantizer.dictionary columns,
        GeneralPaperComputedThreshold.table (GeneralPaperRowQuantizer.dictionary columns) (GeneralPaperRetainedFieldValues.selector values) S,
        GeneralPaperComputedThreshold.compute (GeneralPaperRowQuantizer.dictionary columns) (opposingProxy/ownBudget)
          (GeneralPaperRetainedFieldValues.selector values) S⟩ : GeneralPaperTransferPreparation.Prepared T m K S) := by
  dsimp only [run]
  rw [dp_data,fields_data bits model W depth S columns _ hK hCap,threshold_data]
  rfl

theorem matrix_data {T m K : ℕ} (bits : Bool) (model : RationalCostModel) (W depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (values : GeneralPaperRetainedFieldValues.Values m)
    (ownBudget opposingProxy : ℚ) :
    (run bits model W depth S hK columns values ownBudget opposingProxy).1.matrix=
      (GeneralPaperPhysicalScoreMatrix.run bits model W depth columns (GeneralPaperRetainedFieldValues.selector values) S).1 := rfl

theorem maximum_data {T m K : ℕ} (bits : Bool) (model : RationalCostModel) (W depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (values : GeneralPaperRetainedFieldValues.Values m)
    (ownBudget opposingProxy : ℚ) (hCap : S<2^depth) :
    (run bits model W depth S hK columns values ownBudget opposingProxy).1.maximum=
      GeneralPaperScoreMaximum.maximum (GeneralPaperRetainedFieldValues.selector values) S :=
  GeneralPaperStoredScoreMaximum.actual_data bits model W depth columns _ S hK hCap

end Blotto.GeneralPaperRetainedTransferPreparation
