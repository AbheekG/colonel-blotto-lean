import Blotto.NativeArrayConversionCore
import Blotto.BinaryPRGHeapTraceUsage

/-! An actual descending read of a native array into a list. The source path
uses the pinned Array.foldr/toList index order and returns the copied list;
the parallel work path measures the same reads. Native get/reference-bit and
scalar arithmetic prices remain separate from the Boolean/list visit charge. -/
namespace Blotto.BinaryArrayProjectionLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage NativeArrayConversionCore

def loopWithTrace {α : Type*} (data : Array α) (acc : List α) :
    (remaining : ℕ) → remaining ≤ data.size → List α × Trace
  | 0,_ => (acc,[.frames 1])
  | remaining+1,h =>
      let later := loopWithTrace data (data[remaining]'(by omega)::acc) remaining (by omega)
      (later.1,[.frames 1,.listAllocation 1,.arrayAllocation 4] ++ under 1 later.2)

theorem loop_state {α : Type*} (data : Array α) (acc : List α)
    (remaining : ℕ) (h : remaining ≤ data.size) :
    (loopWithTrace data acc remaining h).1 = (readLoop data acc remaining h).1 := by
  induction remaining generalizing acc with
  | zero => rfl
  | succ remaining ih =>
      exact ih (data[remaining]'(by omega)::acc) (by omega)

theorem loop_bounds {α : Type*} (data : Array α) (acc : List α)
    (remaining : ℕ) (h : remaining ≤ data.size) :
    listCells (loopWithTrace data acc remaining h).2 = remaining ∧
    arraySlots (loopWithTrace data acc remaining h).2 = 4*remaining ∧
    framePeak (loopWithTrace data acc remaining h).2 ≤ remaining+1 := by
  induction remaining generalizing acc with
  | zero => simp [loopWithTrace,listCells,arraySlots,framePeak]
  | succ remaining ih =>
      have ht := ih (data[remaining]'(by omega)::acc) (by omega)
      have hf := framePeak_under 1 (loopWithTrace data (data[remaining]'(by omega)::acc) remaining (by omega)).2
      simp only [loopWithTrace,listCells_append,arraySlots_append,framePeak_append,
        listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
      exact ⟨by omega,by omega,by omega⟩

def readWithTrace {α : Type*} (data : Array α) : List α × Trace :=
  loopWithTrace data [] data.size (Nat.le_refl _)

theorem read_state {α : Type*} (data : Array α) :
    (readWithTrace data).1 = data.toList := by
  rw [readWithTrace,loop_state]
  exact NativeArrayConversionCore.read_state data

theorem read_usage {α : Type*} (data : Array α) :
    usage (readWithTrace data).2 ≤ 6*data.size+1 := by
  have h := loop_bounds data [] data.size (Nat.le_refl _)
  change listCells (readWithTrace data).2 = data.size ∧
    arraySlots (readWithTrace data).2 = 4*data.size ∧
    framePeak (readWithTrace data).2 ≤ data.size+1 at h
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells
  omega

def loopWithWork {α : Type*} (data : Array α) (acc : List α) :
    (remaining : ℕ) → remaining ≤ data.size → List α × ℕ
  | 0,_ => (acc,2)
  | remaining+1,h =>
      let later := loopWithWork data (data[remaining]'(by omega)::acc) remaining (by omega)
      (later.1,later.2+8)

theorem loop_work_state {α : Type*} (data : Array α) (acc : List α)
    (remaining : ℕ) (h : remaining ≤ data.size) :
    (loopWithWork data acc remaining h).1 = (loopWithTrace data acc remaining h).1 := by
  induction remaining generalizing acc with
  | zero => rfl
  | succ remaining ih =>
      exact ih (data[remaining]'(by omega)::acc) (by omega)

theorem loop_work {α : Type*} (data : Array α) (acc : List α)
    (remaining : ℕ) (h : remaining ≤ data.size) :
    (loopWithWork data acc remaining h).2 = 8*remaining+2 := by
  induction remaining generalizing acc with
  | zero => rfl
  | succ remaining ih =>
      simp only [loopWithWork,ih]
      omega

def readWithWork {α : Type*} (data : Array α) : List α × ℕ :=
  loopWithWork data [] data.size (Nat.le_refl _)

theorem read_work_state {α : Type*} (data : Array α) :
    (readWithWork data).1 = (readWithTrace data).1 := loop_work_state data [] _ _

theorem read_work {α : Type*} (data : Array α) :
    (readWithWork data).2 = 8*data.size+2 := loop_work data [] _ _

theorem read_index_sequence {α : Type*} (data : Array α) :
    (NativeArrayConversionCore.read data).2.filterMap ReadSnapshot.readIndex =
      (List.range data.size).reverse := NativeArrayConversionCore.read_indices data

theorem read_scalar_width {α : Type*} (data : Array α) :
    ∀ s ∈ (NativeArrayConversionCore.read data).2,
      ∀ value ∈ s.operands data.size,
        binaryWordWidth value ≤ binaryWordWidth (data.size+1) := by
  intro s hs value hv
  exact binaryWordWidth_mono
    ((ReadSnapshot.operand_bound (NativeArrayConversionCore.read_valid data s hs)) value hv)

end Blotto.BinaryArrayProjectionLifetime
