import Blotto.GeneralPaperCachedCircleCommon

/-! Store only sorted representative references per row. Original columns
and one common light-field cache stay resident. A selected draw materializes
its kept-field references once; no full-row view table runs on a draw. -/
namespace Blotto.GeneralPaperCachedCircleRows
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def representatives {T h R K : ℕ} (index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) : FixedArrayTable R ℚ×ℕ :=
  PaperIndexedArrayConstruction.run index A (fun a =>
    let column := columns.read (Fin.natAdd h a)
    (column.anchors.read (column.labels.read i),
      GeneralPaperNaturalPrimitivePrice.binary index (fun a b => a+b) h a.val+128*A))

theorem representatives_data {T h R K : ℕ} (index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) :
    (representatives index A columns i).1=FixedArrayTable.ofFn (fun a =>
      (columns.read (Fin.natAdd h a)).anchors.read ((columns.read (Fin.natAdd h a)).labels.read i)) :=
  PaperIndexedArrayConstruction.run_data _ _ _

def sortedRow {T h R K : ℕ} (price index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) : FixedArrayTable R ℚ×ℕ :=
  let input := representatives index A columns i
  let sorted := GeneralPaperNativeSortedRows.one price index A input.1
  (sorted.1,input.2+sorted.2+64*A)

theorem sorted_data {T h R K : ℕ} (price index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) :
    (sortedRow price index A columns i).1=
      (GeneralPaperNativeSortedRows.one price index A (representatives index A columns i).1).1 := rfl

theorem sorted_origin {T h R K : ℕ} (price index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) (a : Fin R) :
    ∃ j : Fin (h+R),(sortedRow price index A columns i).1.read a=
      (columns.read j).anchors.read ((columns.read j).labels.read i) := by
  let source := (representatives index A columns i).1
  refine ⟨Fin.natAdd h ((GeneralPaperRowSort.order source).read a),?_⟩
  dsimp only [source]
  simp only [sorted_data,GeneralPaperNativeSortedRows.one_data,representatives_data,FixedArrayTable.read_ofFn]

def sortedRows {T h R K : ℕ} (price index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) : FixedArrayTable T (FixedArrayTable R ℚ)×ℕ :=
  PaperIndexedArrayConstruction.run index A (fun i => let row := sortedRow price index A columns i; (row.1,row.2+64*A))

theorem read_sorted {T h R K : ℕ} (price index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) :
    (sortedRows price index A columns).1.read i=(sortedRow price index A columns i).1 := by
  unfold sortedRows
  rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]

structure Rows (T h R K : ℕ) where
  columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)
  sorted : FixedArrayTable T (FixedArrayTable R ℚ)

def prepare {T h R K : ℕ} (price index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) : Rows T h R K×ℕ :=
  let sorted := sortedRows price index A columns
  (⟨columns,sorted.1⟩,sorted.2+64*A)

theorem columns_data {T h R K : ℕ} (price index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) :
    (prepare price index A columns).1.columns=columns := rfl

def kept {T h R K : ℕ} (index : ℕ → ℕ) (A : ℕ) (rows : Rows T h R K) (i : Fin T) : FixedArrayTable h ℚ×ℕ :=
  PaperIndexedArrayConstruction.run index A (fun j =>
    let column := rows.columns.read (Fin.castAdd R j)
    (column.anchors.read (column.labels.read i),128*A))

theorem kept_data {T h R K : ℕ} (index : ℕ → ℕ) (A : ℕ) (rows : Rows T h R K) (i : Fin T) :
    (kept index A rows i).1=FixedArrayTable.ofFn (fun j =>
      (rows.columns.read (Fin.castAdd R j)).anchors.read ((rows.columns.read (Fin.castAdd R j)).labels.read i)) :=
  PaperIndexedArrayConstruction.run_data _ _ _

def materialize {T n R K : ℕ} (index : ℕ → ℕ) (A : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (rows : Rows T state.heavy.size R K) (common : GeneralPaperCachedCircleCommon.Cache state.light.size) (i : Fin T) :
    GeneralPaperNamedCircleExecution.Prepared state R×ℕ :=
  let selected := kept index A rows i
  (GeneralPaperCachedCircleCommon.view state common selected.1 (rows.sorted.read i),selected.2+64*A)

theorem row_view {T n R K : ℕ} (price index : ℕ → ℕ) (A W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (weights : FixedArrayTable state.light.size ℕ)
    (columns : FixedArrayTable (state.heavy.size+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) :
    GeneralPaperCachedCircleCommon.view state (GeneralPaperCachedCircleCommon.run price index A R W weights).1
      (FixedArrayTable.ofFn (fun j => (columns.read (Fin.castAdd R j)).anchors.read ((columns.read (Fin.castAdd R j)).labels.read i)))
      (sortedRow price index A columns i).1=
        (GeneralPaperStoredCirclePreparation.row price index A W state weights (GeneralPaperStoredDictionaryRows.row index A columns i).1).1 := by
  have hParts := GeneralPaperStoredCirclePreparation.split_data index A (GeneralPaperStoredDictionaryRows.row index A columns i).1
  rw [GeneralPaperStoredDictionaryRows.row_data] at hParts
  simp only [FixedArrayTable.read_ofFn] at hParts
  dsimp only [GeneralPaperCachedCircleCommon.view,GeneralPaperCachedCircleCommon.run,sortedRow,
    GeneralPaperStoredCirclePreparation.row,GeneralPaperNamedCircleExecution.prepare]
  rw [GeneralPaperStoredDictionaryRows.row_data,hParts,representatives_data]

theorem materialize_data {T n R K : ℕ} (price index selectedIndex : ℕ → ℕ) (A Ap W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (weights : FixedArrayTable state.light.size ℕ)
    (columns : FixedArrayTable (state.heavy.size+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) :
    (materialize selectedIndex Ap state (prepare price index A columns).1
      (GeneralPaperCachedCircleCommon.run price index A R W weights).1 i).1=
        (GeneralPaperStoredCirclePreparation.fromColumns price index A W state weights columns).1.read i := by
  dsimp only [materialize]
  rw [kept_data]
  change GeneralPaperCachedCircleCommon.view state _ _ ((sortedRows price index A columns).1.read i)=_
  rw [read_sorted]
  exact (row_view price index A W state weights columns i).trans
    (GeneralPaperStoredCirclePreparation.columns_row price index A W state weights columns i).symm

structure Pair {n : ℕ} (T R K : ℕ) (state : GeneralPaperLightFieldScan.State n) where
  common : GeneralPaperCachedCircleCommon.Cache state.light.size
  rich : Rows T state.heavy.size R K
  poor : Rows T state.heavy.size R K

def pair {n T K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K) :
    Pair T o.representatives K o.classified×ℕ :=
  let common := GeneralPaperCachedCircleCommon.fromOriginal price index A o
  let rich := prepare price index A (GeneralPaperPhysicalFieldCast.columns hm columns.rich)
  let poor := prepare price index A (GeneralPaperPhysicalFieldCast.columns hm columns.poor)
  (⟨common.1,rich.1,poor.1⟩,common.2+rich.2+poor.2+128*A)

theorem pair_common {n T K : ℕ} (price index : ℕ → ℕ) (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K) :
    (pair price index A o hm columns).1.common=(GeneralPaperCachedCircleCommon.fromOriginal price index A o).1 := rfl

theorem pair_materialize {n T K : ℕ} (price index selectedIndex : ℕ → ℕ) (A Ap : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K)
    (reciprocal : Bool) (i : Fin T) :
    let prepared := (pair price index A o hm columns).1
    (materialize selectedIndex Ap o.classified (if reciprocal then prepared.poor else prepared.rich) prepared.common i).1=
      (GeneralPaperOriginalCirclePreparation.run price index A o hm (if reciprocal then columns.poor else columns.rich)).1.read i := by
  cases reciprocal <;> dsimp only [pair,Bool.false_eq_true,ite_false,ite_true]
  all_goals exact materialize_data price index selectedIndex A Ap o.classified.lightWeight o.classified _ _ i

end Blotto.GeneralPaperCachedCircleRows
