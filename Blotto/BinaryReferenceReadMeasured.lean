import Blotto.BinaryHeapReadMeasured

/-! Physical slot lookup consumes each returned field suffix and decremented
Boolean index once. Data, source traces and conservative source charges are
joined structurally, including malformed/EOF paths. Complete pointer-width
reservations are ghost annotations, not native observer-evaluation prices. -/

namespace Blotto.BinaryReferenceReadMeasured
open BinaryPRGWordStoreHeap BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 2500000

def read (tape index : List Bool) : (Option Pointer × Trace) × ℕ :=
  let field := BinaryHeapTapeMeasured.readField tape
  match hField : field.1.1 with
  | none => ((none,wrap 16 2 [field.1.2]),field.2.work+4)
  | some parsed =>
      let tested := BooleanFreshSeedMeasured.scan index
      if tested.1.1 = true then
        let decremented := BooleanFreshSeedMeasured.predecessor index
        let later := read parsed.2 decremented.1.1
        ((later.1.1,wrap 48 2 [field.1.2,tested.1.2,decremented.1.2,later.1.2]),
          field.2.work+(index.length+1)+decremented.2+later.2+8)
      else ((some parsed.1,wrap 32 2 [field.1.2,tested.1.2]),field.2.work+(index.length+1)+8)
termination_by tape.length
decreasing_by
  apply BinaryReferenceVector.readField_strict tape parsed
  change (BinaryHeapTapeMeasured.readField tape).1.1 = some parsed at hField
  exact (BinaryPRGWordStoreHeapMachine.readFieldWithWork_erasure tape).symm.trans
    ((BinaryHeapTapeMeasured.readField_data tape).symm.trans hField)

theorem read_erases (tape index : List Bool) :
    (read tape index).1 = BinaryReferenceVectorLifetime.readWithTrace tape index := by
  have hAll : ∀ length,∀ tape : List Bool,tape.length = length → ∀ index,
      (read tape index).1 = BinaryReferenceVectorLifetime.readWithTrace tape index := by
    intro length
    induction length using Nat.strong_induction_on with
    | h length ih =>
        intro tape hLength index
        rw [read,BinaryReferenceVectorLifetime.readWithTrace]
        dsimp only
        rw [BinaryHeapTapeMeasured.readField_erases]
        cases hParsed : (BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace tape).1 with
        | none => simp only
        | some parsed =>
            have hLess := BinaryReferenceVector.readField_strict tape parsed
              ((BinaryPRGWordStoreHeapMachine.readFieldWithWork_erasure tape).symm.trans
                ((BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace_erasure tape).symm.trans hParsed))
            simp only [BooleanFreshSeedMeasured.scan_erases,BooleanFreshSeedMeasured.predecessor_erases]
            split
            · simp only [ih _ (by omega) parsed.2 rfl]
            · rfl
  exact hAll _ tape rfl index

theorem read_data (tape index : List Bool) :
    (read tape index).1.1 = (BinaryReferenceVector.readWithWork tape index).1 := by
  have h := congrArg Prod.fst (read_erases tape index)
  exact h.trans (BinaryReferenceVectorLifetime.read_state tape index)

theorem read_work (tape index : List Bool) :
    (read tape index).2 = (BinaryReferenceVector.readWithWork tape index).2 := by
  have hAll : ∀ length,∀ tape : List Bool,tape.length = length → ∀ index,
      (read tape index).2 = (BinaryReferenceVector.readWithWork tape index).2 := by
    intro length
    induction length using Nat.strong_induction_on with
    | h length ih =>
        intro tape hLength index
        rw [read,BinaryReferenceVector.readWithWork]
        dsimp only
        rw [BinaryHeapTapeMeasured.readField_data]
        simp only [BinaryHeapTapeMeasured.readField_charge]
        cases hParsed : (BinaryPRGWordStoreHeapMachine.readFieldWithWork tape).1 with
        | none => simp only
        | some parsed =>
            have hLess := BinaryReferenceVector.readField_strict tape parsed
              ((BinaryPRGWordStoreHeapMachine.readFieldWithWork_erasure tape).symm.trans hParsed)
            simp only [BooleanFreshSeedMeasured.scan_erases,BinaryBooleanPrimitiveLifetime.scanWithTrace_erases,
              BooleanFreshSeedMeasured.predecessor_erases,BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure,
              BooleanFreshSeedMeasured.predecessor_work,BinaryStoredCountdown.predecessorWithWork]
            split
            · simp only [ih _ (by omega) parsed.2 rfl]
            · rfl
  exact hAll _ tape rfl index

theorem read_bound (tape index : List Bool) :
    (read tape index).2 ≤ BinaryReferenceVector.readBound tape.length index.length := by
  rw [read_work]
  exact BinaryReferenceVector.readWithWork_bound tape index

theorem read_all_prefix (tape index : List Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (read tape index).1.2 steps ≤
        borrowed+64*BinaryReferenceVector.readBound tape.length index.length ∧
      framePeak ((read tape index).1.2.take steps) ≤
        64*BinaryReferenceVector.readBound tape.length index.length := by
  rw [read_erases]
  exact BinaryReferenceVectorLifetime.read_all_prefix tape index borrowed steps

end Blotto.BinaryReferenceReadMeasured
