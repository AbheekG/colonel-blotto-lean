import Blotto.GeneralPaperPreparedCircleModels

/-! Retain one prepared circle row for each actual unit source row. Heavy
and representative references are split once, and every stored row owns
its native sort, coefficients and metadata. Draws read prepared rows only. -/
namespace Blotto.GeneralPaperStoredCirclePreparation
open GeneralPaperNamedCircleExecution
set_option autoImplicit false
set_option maxHeartbeats 2800000

def split {h R : ℕ} (index : ℕ → ℕ) (A : ℕ) (row : FixedArrayTable (h+R) ℚ) :
    (FixedArrayTable h ℚ×FixedArrayTable R ℚ)×ℕ :=
  let kept := PaperIndexedArrayConstruction.run index A (fun j => (row.read (Fin.castAdd R j),64*A))
  let representatives := PaperIndexedArrayConstruction.run index A (fun a =>
    (row.read (Fin.natAdd h a),GeneralPaperNaturalPrimitivePrice.binary index (fun a b => a+b) h a.val+64*A))
  ((kept.1,representatives.1),kept.2+representatives.2+32*A)

theorem split_data {h R : ℕ} (index : ℕ → ℕ) (A : ℕ) (row : FixedArrayTable (h+R) ℚ) :
    (split index A row).1=(FixedArrayTable.ofFn (fun j => row.read (Fin.castAdd R j)),
      FixedArrayTable.ofFn (fun a => row.read (Fin.natAdd h a))) := by
  dsimp only [split]
  rw [PaperIndexedArrayConstruction.run_data,PaperIndexedArrayConstruction.run_data]

theorem split_real {h R : ℕ} (index : ℕ → ℕ) (A : ℕ) (row : FixedArrayTable (h+R) ℚ) :
    Fin.addCases (fun j => ((split index A row).1.1.read j:ℝ)) (fun a => ((split index A row).1.2.read a:ℝ))=
      (fun j => (row.read j:ℝ)) := by
  rw [split_data]
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [Fin.addCases_left,FixedArrayTable.read_ofFn]
  · intro i
    simp only [Fin.addCases_right,FixedArrayTable.read_ofFn]

def row {n R : ℕ} (price index : ℕ → ℕ) (A W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (weights : FixedArrayTable state.light.size ℕ) (input : FixedArrayTable (state.heavy.size+R) ℚ) : Prepared state R×ℕ :=
  let parts := split index A input
  let prepared := prepare price index A W state parts.1.1 parts.1.2 weights
  (prepared.1,parts.2+prepared.2+32*A)

theorem row_data {n R : ℕ} (price index : ℕ → ℕ) (A W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (weights : FixedArrayTable state.light.size ℕ) (input : FixedArrayTable (state.heavy.size+R) ℚ) :
    (row price index A W state weights input).1=
      (prepare (fun _ => 1) (fun _ => 1) 1 W state
        (FixedArrayTable.ofFn (fun j => input.read (Fin.castAdd R j)))
        (FixedArrayTable.ofFn (fun a => input.read (Fin.natAdd state.heavy.size a))) weights).1 := by
  change (prepare price index A W state (split index A input).1.1 (split index A input).1.2 weights).1=_
  rw [split_data]
  exact GeneralPaperPreparedCircleModels.data price (fun _ => 1) index (fun _ => 1) A 1 W state _ _ weights

def run {T n R : ℕ} (price index : ℕ → ℕ) (A W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (weights : FixedArrayTable state.light.size ℕ) (inputs : FixedArrayTable T (FixedArrayTable (state.heavy.size+R) ℚ)) :
    FixedArrayTable T (Prepared state R)×ℕ :=
  PaperIndexedArrayConstruction.run index A (fun i => let prepared := row price index A W state weights (inputs.read i);
    (prepared.1,prepared.2+64*A))

theorem read_row {T n R : ℕ} (price index : ℕ → ℕ) (A W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (weights : FixedArrayTable state.light.size ℕ) (inputs : FixedArrayTable T (FixedArrayTable (state.heavy.size+R) ℚ)) (i : Fin T) :
    (run price index A W state weights inputs).1.read i=(row price index A W state weights (inputs.read i)).1 := by
  unfold run
  rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]

def fromColumns {T n R K : ℕ} (price index : ℕ → ℕ) (A W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (weights : FixedArrayTable state.light.size ℕ)
    (columns : FixedArrayTable (state.heavy.size+R) (GeneralPaperQuantizedColumn.Column T K)) : FixedArrayTable T (Prepared state R)×ℕ :=
  let inputs := GeneralPaperStoredDictionaryRows.run index A columns
  let prepared := run price index A W state weights inputs.1
  (prepared.1,inputs.2+prepared.2+64*A)

theorem columns_row {T n R K : ℕ} (price index : ℕ → ℕ) (A W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (weights : FixedArrayTable state.light.size ℕ)
    (columns : FixedArrayTable (state.heavy.size+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) :
    (fromColumns price index A W state weights columns).1.read i=
      (row price index A W state weights (GeneralPaperStoredDictionaryRows.row index A columns i).1).1 := by
  change (run price index A W state weights (GeneralPaperStoredDictionaryRows.run index A columns).1).1.read i=_
  rw [read_row,GeneralPaperStoredDictionaryRows.data,FixedArrayTable.read_ofFn,GeneralPaperStoredDictionaryRows.row_data]

def draw {T n R : ℕ} (model : RationalCostModel) (W S : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (hR : 0<R) (c : ℚ) (prepared : FixedArrayTable T (Prepared state R)) (i : Fin T) (l : Fin S) : FixedArrayTable n ℚ×ℕ :=
  let output := drawArithmetic model W S state hR c (prepared.read i) l
  (output.1,output.2+64)

end Blotto.GeneralPaperStoredCirclePreparation
