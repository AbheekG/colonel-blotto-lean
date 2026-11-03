import Blotto.BinaryPromiseArithmeticEntryWork
import Blotto.BinaryPromiseOpcodePreparation

/-! Proof-only entry charges follow actual numerical ratio/two-pass results
and the actual promise outcome. Flattened child reservations retain every
entry charge; rejected preparation has zero numerical entry contribution. -/
namespace Blotto.BinaryPreparationArithmeticEntryWork
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryTracePlanMeasured
open BinaryRationalOpcode BinaryPRGRecognition BinaryPRGPreparation
open BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 5000000

def entryCells {α : Type*} : List (α × Trace) → ℕ
  | [] => 0
  | entry::rest => listCells entry.2+entryCells rest

theorem entryCells_flatten {α : Type*} (entries : List (α × Trace)) :
    entryCells entries = listCells ((BinaryLifetimeArray.mapDirect Prod.snd entries).flatten) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp only [entryCells,BinaryLifetimeArray.mapDirect,List.flatten_cons,listCells_append,ih]

theorem entryCells_fromEntries {α : Type*} (n : ℕ) (entries : List (α × Trace)) (hEntries : entries.length=n) :
    entryCells entries = listCells (BinaryLifetimeEntriesMeasured.fromEntries n entries hEntries).1.2 := by
  rw [BinaryLifetimeEntriesMeasured.fromEntries_erases]
  simp only [BinaryLifetimeArray.fromEntries,listCells_append,listCells_under,listCells,
    BinaryLifetimeFlattenList.flattenDirect_result,← entryCells_flatten,Nat.zero_add]

def mapCost {α : Type*} (cost : α → ℕ) : List α → ℕ
  | [] => 0
  | item::rest => cost item+mapCost cost rest

theorem map_bound {α β : Type*} (produce : α → ((β × Trace) × ℕ) × ℕ) (cost : α → ℕ)
    (h : ∀ item,cost item ≤ 2*listCells (produce item).1.1.2) (items : List α) :
    mapCost cost items ≤ 2*entryCells (BinaryNumericalOpcodeEntries.map produce items).1.1 := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      have hh := h item
      simp only [mapCost,BinaryNumericalOpcodeEntries.map,entryCells]
      omega

theorem opcode_bound (op : RealArithmeticOp) (a b : SignedWord) :
    BinaryArithmeticEntryWork.raw op a b ≤ 2*listCells (BinaryNumericalOpcodeEntries.opcode op a b).1.1.2 := by
  have h := BinaryArithmeticEntryWork.normalized_plan op a b 0
  simpa only [BinaryNumericalOpcodeEntries.opcode,BinaryNormalizationPlan.apply,
    BinaryNormalizationPlan.finishMeasured,BinaryNumericalReadbackPlan.finish,emitFull_erases,
    emit_data,List.append_nil] using h

def preparation {n : ℕ} (input : Input n) (rows : List SignedWord) : ℕ :=
  let ratio := (BinaryNumericalOpcodeEntries.opcode .div input.b input.a).1
  let lengths := (BinaryNumericalOpcodeEntries.map (BinaryNumericalOpcodeEntries.opcode .mul two) rows).1
  BinaryArithmeticEntryWork.raw .div input.b input.a+
    mapCost (BinaryArithmeticEntryWork.raw .mul two) rows+
    mapCost (fun item : SignedWord × Trace => BinaryArithmeticEntryWork.raw .mul ratio.1.1 item.1) lengths.1

theorem entries_bound {n : ℕ} (input : Input n) (rows : List SignedWord) (hRows : rows=List.ofFn input.values.read) :
    let entries := (BinaryNumericalOpcodeEntries.prepare input rows hRows).1.1
    preparation input rows ≤ 2*(listCells entries.ratio.2+entryCells entries.lengths+entryCells entries.poor) := by
  have hr := opcode_bound .div input.b input.a
  have hl := map_bound (BinaryNumericalOpcodeEntries.opcode .mul two) (BinaryArithmeticEntryWork.raw .mul two)
    (fun word => opcode_bound .mul two word) rows
  have hp := map_bound
    (fun item : SignedWord × Trace => BinaryNumericalOpcodeEntries.opcode .mul
      (BinaryNumericalOpcodeEntries.opcode .div input.b input.a).1.1.1 item.1)
    (fun item : SignedWord × Trace => BinaryArithmeticEntryWork.raw .mul
      (BinaryNumericalOpcodeEntries.opcode .div input.b input.a).1.1.1 item.1)
    (fun item => opcode_bound _ _ _)
    (BinaryNumericalOpcodeEntries.map (BinaryNumericalOpcodeEntries.opcode .mul two) rows).1.1
  simp only [preparation,BinaryNumericalOpcodeEntries.prepare]
  omega

theorem preparation_bound {n : ℕ} (input : Input n) (rows : List SignedWord) (hRows : rows=List.ofFn input.values.read) :
    preparation input rows ≤ 2*listCells (BinaryNumericalOpcodePreparation.prepare input rows hRows).1.1.2 := by
  let entries := (BinaryNumericalOpcodeEntries.prepare input rows hRows).1.1
  have he := entries_bound input rows hRows
  have hl := entryCells_fromEntries n entries.lengths entries.lengths_size
  have hp := entryCells_fromEntries n entries.poor entries.poor_size
  dsimp only [entries] at hl hp
  simp only [BinaryNumericalOpcodePreparation.prepare,wrapList,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def checked {n : ℕ} (input : Input n) (rows : List SignedWord) : ℕ :=
  BinaryPromiseArithmeticEntryWork.checkRows input rows 0+
    if (BinaryPromiseCheckPlan.checkRows input rows).1.1.1 then preparation input rows else 0

theorem checked_reject {n : ℕ} (input : Input n) (rows : List SignedWord)
    (h : (BinaryPromiseCheckPlan.checkRows input rows).1.1.1=false) :
    checked input rows = BinaryPromiseArithmeticEntryWork.checkRows input rows 0 := by
  simp only [checked,h,Bool.false_eq_true,ite_false,Nat.add_zero]

theorem checked_bound {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows=List.ofFn input.values.read) :
    checked input rows ≤ 2*listCells (BinaryPromiseOpcodePreparation.checked input hC rows hRows).1.1.1.2 := by
  have hp := BinaryPromiseArithmeticEntryWork.emitted_bound input rows
  have hn := preparation_bound input rows hRows
  simp only [checked,BinaryPromiseOpcodePreparation.checked]
  split <;> simp only [wrap,combine,listCells_append,listCells_under,listCells] <;> omega

theorem checked_with_work {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows=List.ofFn input.values.read) :
    let produced := BinaryPromiseOpcodePreparation.checked input hC rows hRows
    checked input rows+produced.1.1.2+produced.1.2+produced.2 ≤
      2*(listCells produced.1.1.1.2+produced.1.1.2+produced.1.2+produced.2) := by
  have h := checked_bound input hC rows hRows
  dsimp only
  omega

end Blotto.BinaryPreparationArithmeticEntryWork
