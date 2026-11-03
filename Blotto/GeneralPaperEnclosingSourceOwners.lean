import Blotto.GeneralPaperSourceEndpointFractionConstructionStorageReachedRates
import Blotto.GeneralPaperSourceScoreStorage

/-! Complete enclosing source rows, physical columns and prepared return.
The native dictionary is a view of the counted columns. Full strict-score
table, original score matrix and scalar return fields remain owned. This
observer covers resident payload; constructor scratch and caller work
fields remain separate joins. -/
namespace Blotto.GeneralPaperEnclosingSourceOwners
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def rowsFoot {T m : ℕ} (W : ℕ) (rows : FixedArrayTable T (FixedArrayTable m ℚ)) : ℕ :=
  arrayFootprint W (arrayFootprint W rationalWordWidth) rows
def rowsProfile (W T m R : ℕ) : ℕ := arrayProfile W T (arrayProfile W m R)
def columnFoot {T K : ℕ} (W : ℕ) (c : GeneralPaperQuantizedColumn.Column T K) : ℕ :=
  arrayFootprint W (fun l : Fin K => natBits l.val) c.labels+arrayFootprint W rationalWordWidth c.anchors+32*W
def columnProfile (W T K R : ℕ) : ℕ := arrayProfile W T (natBits K)+arrayProfile W K R+32*W
def columnsFoot {T m K : ℕ} (W : ℕ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) : ℕ :=
  arrayFootprint W (columnFoot W) columns
def columnsProfile (W T m K R : ℕ) : ℕ := arrayProfile W m (columnProfile W T K R)
def recordFoot {T m K S : ℕ} (W : ℕ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (out : GeneralPaperRetainedTransferPreparation.Output T m K S)
    (_hView : out.prepared.dictionary=GeneralPaperRowQuantizer.dictionary columns) : ℕ :=
  columnsFoot W columns+GeneralPaperScoreTableStorage.tableFootprint W out.prepared.table+
    GeneralPaperEncodedScoreMatrixStorage.matrixFootprint W out.matrix+
    natBits out.prepared.threshold+natBits out.maximum+rationalWordWidth out.budget+160*W
def window {T m K : ℕ} (model : RationalCostModel) (W depth S : ℕ) (hK : 0<K)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) : ℕ :=
  rowsFoot W rows+recordFoot W columns
    (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1 rfl+128*W
def profile (W T m K S R P Budget Matrix : ℕ) : ℕ :=
  rowsProfile W T m R+columnsProfile W T m K R+GeneralPaperScoreTableStorage.tableProfile W K S m P+
    Matrix+2*natBits S+Budget+288*W

theorem rows_bound {T m : ℕ} (W R : ℕ) (rows : FixedArrayTable T (FixedArrayTable m ℚ))
    (h : ∀ i j,rationalWordWidth ((rows.read i).read j)≤R) : rowsFoot W rows≤rowsProfile W T m R := by
  exact array_bound W _ _ rows (fun i => array_bound W R rationalWordWidth (rows.read i) (h i))

theorem column_bound {T K : ℕ} (W R : ℕ) (c : GeneralPaperQuantizedColumn.Column T K)
    (h : ∀ l,rationalWordWidth (c.anchors.read l)≤R) : columnFoot W c≤columnProfile W T K R := by
  have hLabels := array_bound W (natBits K) (fun l : Fin K => natBits l.val) c.labels
    (fun i => Nat.add_le_add_left (binaryWordWidth_mono (c.labels.read i).isLt.le) 1)
  have hAnchors := array_bound W R rationalWordWidth c.anchors h
  unfold columnFoot columnProfile
  omega

theorem columns_bound {T m K : ℕ} (W R : ℕ) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (h : ∀ j l,rationalWordWidth ((columns.read j).anchors.read l)≤R) : columnsFoot W columns≤columnsProfile W T m K R :=
  array_bound W _ _ columns (fun j => column_bound W R (columns.read j) (h j))

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W depth S R P Budget Matrix : ℕ) (hK : 0<K)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (hRows : ∀ i j,rationalWordWidth ((rows.read i).read j)≤R)
    (hColumns : ∀ j l,rationalWordWidth ((columns.read j).anchors.read l)≤R)
    (hTable : GeneralPaperScoreTableStorage.tableFootprint W
      (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.prepared.table≤
        GeneralPaperScoreTableStorage.tableProfile W K S m P)
    (hMatrix : GeneralPaperEncodedScoreMatrixStorage.matrixFootprint W
      (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.matrix≤Matrix)
    (hThreshold : (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.prepared.threshold≤S)
    (hMaximum : (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.maximum≤S)
    (hBudget : rationalWordWidth (opposing/own)≤Budget) :
    window model W depth S hK rows columns values own opposing≤profile W T m K S R P Budget Matrix := by
  have hR := rows_bound W R rows hRows
  have hC := columns_bound W R columns hColumns
  have ht : natBits (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.prepared.threshold≤natBits S :=
    Nat.add_le_add_left (binaryWordWidth_mono hThreshold) 1
  have hm : natBits (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.maximum≤natBits S :=
    Nat.add_le_add_left (binaryWordWidth_mono hMaximum) 1
  change rationalWordWidth (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.budget≤Budget at hBudget
  unfold window recordFoot profile
  omega

end Blotto.GeneralPaperEnclosingSourceOwners
