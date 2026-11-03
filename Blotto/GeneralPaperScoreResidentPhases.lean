import Blotto.GeneralPaperScoreMatrixConstructionStorage
import Blotto.GeneralPaperScoreInitialStorage

/-! Retain the single actual physical matrix and its borrowed field-list
container across initial-table construction, native DP layers and the strict
budget scan. The table is counted once during the threshold scan. These
phase windows exclude physical-column residency, matrix-entry arithmetic,
the stored-maximum pass and the remaining endpoint/compiler phases. -/
namespace Blotto.GeneralPaperScoreResidentPhases
open GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedScoreMatrixStorage GeneralPaperSourceScoreStorage GeneralPaperScoreTableStorage
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192

def resident {T m K : ℕ} (model : RationalCostModel) (W depth S : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) : ℕ :=
  let matrix := (GeneralPaperPhysicalScoreMatrix.run true model W depth columns (GeneralPaperRetainedFieldValues.selector values) S).1
  matrixFootprint W matrix+listFootprint W (fun _ : Field K => 0) matrix.data.toList+256*W

def residentProfile (W m K S A : ℕ) : ℕ := matrixProfile W m K S A+m*(2*W)+32*W+256*W

theorem resident_bound {T m K : ℕ} (model : RationalCostModel) (W depth S A : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (hCap : S<2^depth)
    (ha : ∀ j l,RationalHeight ((columns.read j).anchors.read l) A) :
    resident model W depth S columns values≤residentProfile W m K S A := by
  have hm := native_matrix true model W depth S A columns (GeneralPaperRetainedFieldValues.selector values) hK hCap ha
  unfold resident residentProfile
  dsimp only
  rw [borrowed_fields]
  omega

theorem retained_matrix {T m K : ℕ} (model : RationalCostModel) (W depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) :
    resident model W depth S columns values=
      let matrix := (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.matrix
      matrixFootprint W matrix+listFootprint W (fun _ : Field K => 0) matrix.data.toList+256*W := rfl

theorem initial_with_matrix {T m K : ℕ} (model : RationalCostModel) (W depth S A : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (hCap : S<2^depth)
    (ha : ∀ j l,RationalHeight ((columns.read j).anchors.read l) A)
    (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) (count : ℕ) (hc : count≤S+1) :
    resident model W depth S columns values+
      GeneralPaperScoreLifetimeStorage.callerFrames model W S (matrixFields model W depth S columns values)+
      GeneralPaperScoreInitialStorage.window model W K S count hc≤
        residentProfile W m K S A+GeneralPaperScoreLifetimeStorage.callerProfile model W K S A m+
          GeneralPaperScoreInitialStorage.profile W K S := by
  have hm := resident_bound model W depth S A hK columns values hCap ha
  have hf := GeneralPaperScoreLifetimeStorage.caller_profile model W S A m _
    (fields_height model W depth S A hK columns values hCap ha) (fields_length model W depth S columns values).le hW hIndex
  have hi := GeneralPaperScoreInitialStorage.bounded model W K S hW hIndex count hc
  exact Nat.add_le_add (Nat.add_le_add hm hf) hi

theorem layer_with_matrix {T m K S : ℕ} (model : RationalCostModel) (W depth A : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (hCap : S<2^depth)
    (ha : ∀ j l,RationalHeight ((columns.read j).anchors.read l) A)
    (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W)
    (field : Field K) (rest : List (Field K)) (hSub : (field::rest).Sublist (matrixFields model W depth S columns values))
    (count : ℕ) (hc : count≤S+1) (s : Fin (S+1)) (xs : List (Fin K)) (hXs : xs.length≤K) :
    resident model W depth S columns values+
      (GeneralPaperScoreLifetimeStorage.callerFrames model W S (matrixFields model W depth S columns values)+
        GeneralPaperScoreConstructionStorage.stepWindow model W field rest count hc s xs)≤
      residentProfile W m K S A+GeneralPaperScoreLifetimeStorage.layerProfile model W K S A m :=
  Nat.add_le_add (resident_bound model W depth S A hK columns values hCap ha)
    (GeneralPaperScoreLifetimeStorage.actual_layer model W A m _
      (fields_height model W depth S A hK columns values hCap ha) (fields_length model W depth S columns values).le
      hW hIndex field rest hSub count hc s xs hXs)

def thresholdWindow {T m K : ℕ} (model : RationalCostModel) (W depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) : ℕ :=
  let retained := (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1
  resident model W depth S columns values+
    GeneralPaperThresholdScanStorage.window model W retained.prepared.table retained.budget+256*W

def thresholdProfile (model : RationalCostModel) (W m K S A B : ℕ) : ℕ :=
  residentProfile W m K S A+
    GeneralPaperThresholdScanStorage.profile model W K S m (GeneralPaperScoreBitPrimitive.resourceWidth A m)
      (GeneralPaperThresholdScanBits.comparisonWidth A m B)+256*W

theorem threshold_bound {T m K : ℕ} (model : RationalCostModel) (W depth S A B : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) (hCap : S<2^depth)
    (ha : ∀ j l,RationalHeight ((columns.read j).anchors.read l) A) (hb : RationalHeight (opposing/own) B) :
    thresholdWindow model W depth S hK columns values own opposing≤thresholdProfile model W m K S A B := by
  have hm := resident_bound model W depth S A hK columns values hCap ha
  have ht := GeneralPaperScoreSelectionStorage.run_bounded S A m (matrixFields model W depth S columns values)
    (fields_height model W depth S A hK columns values hCap ha) (fields_length model W depth S columns values).le
  have hs := GeneralPaperThresholdScanStorage.bounded model W m (GeneralPaperScoreBitPrimitive.resourceWidth A m)
    (GeneralPaperThresholdScanBits.comparisonWidth A m B) (run S (matrixFields model W depth S columns values))
    (opposing/own) ht (Nat.le_add_right _ _) ((rationalWordWidth_of_height hb).trans (Nat.le_add_left _ _))
  unfold thresholdWindow
  change resident model W depth S columns values+GeneralPaperThresholdScanStorage.window model W
    (GeneralPaperRetainedTransferPreparation.dp true model W S (matrixFields model W depth S columns values)).1 (opposing/own)+256*W≤_
  rw [GeneralPaperRetainedTransferPreparation.dp_data]
  exact Nat.add_le_add_right (Nat.add_le_add hm hs) _

@[fun_prop]
theorem resident_scaling (m K S A : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => residentProfile W m K S A) := by
  unfold residentProfile
  fun_prop

end Blotto.GeneralPaperScoreResidentPhases
