import Blotto.GeneralPaperNativeDivisibleColumns

/-! Whole unit-row extraction reads actual stored label and anchor arrays.
Each coordinate loads its retained column, original-row label and selected
anchor. The dictionary is an erased semantic view of those same arrays. -/
namespace Blotto.GeneralPaperStoredDictionaryRows
set_option autoImplicit false
set_option maxHeartbeats 2200000

def row {T m K : ℕ} (index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) : FixedArrayTable m ℚ×ℕ :=
  PaperIndexedArrayConstruction.run index A (fun j =>
    let column := columns.read j
    let label := column.labels.read i
    (column.anchors.read label,128*A))

theorem row_data {T m K : ℕ} (index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) :
    (row index A columns i).1=FixedArrayTable.ofFn (fun j => (columns.read j).anchors.read ((columns.read j).labels.read i)) := by
  unfold row
  rw [PaperIndexedArrayConstruction.run_data]

theorem real_row {T m K : ℕ} (index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (hT : 0<T) (i : Fin T) :
    (fun j => ((row index A columns i).1.read j:ℝ))=
      (GeneralPaperDictionary.law (GeneralPaperRowQuantizer.dictionary columns) hT).realRow i := by
  funext j
  rw [row_data,FixedArrayTable.read_ofFn]
  rfl

theorem row_height {T m K : ℕ} (index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (H : ℕ)
    (h : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H) (i : Fin T) (j : Fin m) :
    RationalHeight ((row index A columns i).1.read j) H := by
  rw [row_data,FixedArrayTable.read_ofFn]
  exact h j _

theorem row_work {T m K : ℕ} (index : ℕ → ℕ) (A : ℕ) (hA : 1≤A)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T)
    (hIndex : ∀ j≤m,index (binaryWordWidth (j+1))≤A) :
    (row index A columns i).2≤m*(128*A)+44*(m+1)*A :=
  GeneralPaperControlArrayPrice.indexed_work index A _ _ hA hIndex (fun _ => le_rfl)

def run {T m K : ℕ} (index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) : FixedArrayTable T (FixedArrayTable m ℚ)×ℕ :=
  PaperIndexedArrayConstruction.run index A (fun i => let out := row index A columns i; (out.1,out.2+64*A))

theorem data {T m K : ℕ} (index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    (run index A columns).1=FixedArrayTable.ofFn (fun i => FixedArrayTable.ofFn
      (fun j => (columns.read j).anchors.read ((columns.read j).labels.read i))) := by
  unfold run
  rw [PaperIndexedArrayConstruction.run_data]
  congr 1
  funext i
  exact row_data index A columns i

theorem work {T m K : ℕ} (index : ℕ → ℕ) (A : ℕ) (hA : 1≤A)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (hIndex : ∀ i≤T+m,index (binaryWordWidth (i+1))≤A) :
    (run index A columns).2≤T*(m*(128*A)+44*(m+1)*A+64*A)+44*(T+1)*A :=
  GeneralPaperControlArrayPrice.indexed_work index A _ _ hA (fun i hi => hIndex i (by omega))
    (fun i => Nat.add_le_add_right (row_work index A hA columns i (fun j hj => hIndex j (by omega))) (64*A))

theorem run_real_row {T m K : ℕ} (index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (hT : 0<T) (i : Fin T) :
    (fun j => (((run index A columns).1.read i).read j:ℝ))=
      (GeneralPaperDictionary.law (GeneralPaperRowQuantizer.dictionary columns) hT).realRow i := by
  funext j
  rw [data,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
  rfl

theorem run_height {T m K : ℕ} (index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (H : ℕ)
    (h : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H) (i : Fin T) (j : Fin m) :
    RationalHeight (((run index A columns).1.read i).read j) H := by
  rw [data,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
  exact h j _

theorem run_feasible {T m K : ℕ} (index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (hT : 0<T) (hK : 0<K)
    (h : GeneralPaperTransferPreparation.UnitDictionary (GeneralPaperRowQuantizer.dictionary columns) hT hK) (i : Fin T) :
    Feasible 1 (fun j => (((run index A columns).1.read i).read j:ℝ)) := by
  rw [run_real_row index A columns hT i]
  exact h.feasible i

theorem models_data {T m K : ℕ} (index index' : ℕ → ℕ) (A A' : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) :
    (run index A columns).1=(run index' A' columns).1 := by rw [data,data]

end Blotto.GeneralPaperStoredDictionaryRows
