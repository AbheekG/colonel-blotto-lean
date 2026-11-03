import Blotto.GeneralPaperOriginalDrawBounds
import Blotto.GeneralPaperScoreMatrixBits

/-! Build the full score/resource matrix from actual retained unit-column
arrays once. The dictionary is a view of those arrays. Entry loads and
reference writes are explicitly included with the existing score prices. -/
namespace Blotto.GeneralPaperPhysicalScoreMatrix
open GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 2400000

def run {T m K : ℕ} (bits : Bool) (model : RationalCostModel) (W depth : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (v : RationalFieldSelector m) (S : ℕ) :
    FixedArrayTable m (GeneralPaperExactScoreDP.Field K)×ℕ :=
  let d := GeneralPaperRowQuantizer.dictionary columns
  let matrix := if bits then GeneralPaperScoreMatrixBits.matrixRun model W depth d v S
    else GeneralPaperScoreMatrixWork.matrixRun depth d v S
  (matrix.1,matrix.2+64*m*K*address bits W (m*K+m+K))

theorem data {T m K : ℕ} (bits : Bool) (model : RationalCostModel) (W depth : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (v : RationalFieldSelector m) (S : ℕ)
    (hK : 0<K) (hCap : S<2^depth) :
    (run bits model W depth columns v S).1=FixedArrayTable.ofFn
      (fun j => FixedArrayTable.ofFn (fun l => (GeneralPaperStrictScore.score v S j l,(columns.read j).anchors.read l))) := by
  cases bits with
  | false => exact GeneralPaperScoreMatrixWork.matrix_data depth _ v S hK hCap
  | true => exact GeneralPaperScoreMatrixBits.matrix_data model W depth _ v S hK hCap

theorem models_data {T m K : ℕ} (model : RationalCostModel) (W depth : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (v : RationalFieldSelector m) (S : ℕ)
    (hK : 0<K) (hCap : S<2^depth) :
    (run true model W depth columns v S).1=(run false model 1 depth columns v S).1 := by rw [data,data] <;> assumption

theorem arithmetic_work {T m K : ℕ} (model : RationalCostModel) (depth : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (v : RationalFieldSelector m) (S : ℕ) :
    (run false model 1 depth columns v S).2≤128*(m+1)*(K+1)*(depth+1)+64*m*K := by
  have h := GeneralPaperScoreMatrixWork.matrix_work depth (GeneralPaperRowQuantizer.dictionary columns) v S
  change (GeneralPaperScoreMatrixWork.matrixRun depth _ v S).2+64*m*K*1≤_
  nlinarith only [h]

theorem bit_work {T m K : ℕ} (model : RationalCostModel) (W depth V H : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (v : RationalFieldSelector m) (S : ℕ)
    (hK : 0<K) (hCap : S<2^depth) (hv : ∀ j,RationalHeight (v.weight j) V)
    (hc : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H)
    (hW : 1≤W) (hLabel : binaryWordWidth (K+1)≤W) (hField : binaryWordWidth (m+1)≤W) :
    (run true model W depth columns v S).2≤GeneralPaperScoreMatrixBits.matrixProfile model W V H depth m K+
      64*m*K*arrayWord W (m*K+m+K) := by
  have h := GeneralPaperScoreMatrixBits.matrix_work model W depth (GeneralPaperRowQuantizer.dictionary columns) v S V H
    hK hCap hv hc hW hLabel hField
  exact Nat.add_le_add_right h _

end Blotto.GeneralPaperPhysicalScoreMatrix
