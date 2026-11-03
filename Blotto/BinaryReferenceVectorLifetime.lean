import Blotto.BinaryReferenceVector

/-! Actual field copies and indexed slot reads use the retained Boolean heap
primitives. Every old version stays live. Read storage is bounded by the same
reached primitive work as the executable measured reader; no slot-copy or
access coefficient is accepted from the caller. -/
namespace Blotto.BinaryReferenceVectorLifetime
open BinaryPRGWordStoreHeap BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGHeapPrimitiveLifetime (cells)
set_option maxHeartbeats 2000000

theorem field_usage (pointer : Pointer) :
    usage (BinaryPRGHeapPrimitiveLifetime.fieldWithTrace pointer).2 ≤ 128*(pointer.length+1) := by
  have h := BinaryPRGHeapPrimitiveLifetime.fieldWithTrace_bound pointer
  have hp := BinaryPRGWordStoreHeapMachine.fieldWithWork_price pointer
  unfold usage BinaryPRGHeapPrimitiveLifetime.price at *
  omega

theorem append_usage (first second : List Bool) :
    usage (BinaryPRGHeapPrimitiveLifetime.appendWithTrace first second).2 ≤ 128*(first.length+1) := by
  have h := BinaryPRGHeapPrimitiveLifetime.appendWithTrace_bound first second
  have hp := BinaryPRGWordStoreHeapMachine.appendWithWork_price first second
  unfold usage BinaryPRGHeapPrimitiveLifetime.price at *
  omega

def encodeWithTrace : List Pointer → List Bool × Trace
  | [] => ([],wrap 8 1 [])
  | pointer::rest =>
      let field := BinaryPRGHeapPrimitiveLifetime.fieldWithTrace pointer
      let later := encodeWithTrace rest
      let joined := BinaryPRGHeapPrimitiveLifetime.appendWithTrace field.1 later.1
      (joined.1,wrap 32 2 [field.2,later.2,joined.2])

theorem encode_state (pointers : List Pointer) : (encodeWithTrace pointers).1 = BinaryReferenceVector.encode pointers := by
  induction pointers with
  | nil => rfl
  | cons pointer rest ih => simp only [encodeWithTrace,BinaryReferenceVector.encode,
      BinaryPRGHeapPrimitiveLifetime.appendWithTrace_erasure,BinaryPRGWordStoreHeapMachine.appendWithWork_erasure,
      BinaryPRGHeapPrimitiveLifetime.fieldWithTrace_erasure,BinaryPRGWordStoreHeapMachine.fieldWithWork_erasure,ih]

theorem encode_usage (pointers : List Pointer) :
    usage (encodeWithTrace pointers).2 ≤ 1024*(BinaryReferenceVector.payload pointers+pointers.length+1) := by
  induction pointers with
  | nil => exact (wrap_usage 8 1 []).trans (by simp [BinaryReferenceVector.payload])
  | cons pointer rest ih =>
      have hF := field_usage pointer
      have hA := append_usage (BinaryPRGHeapPrimitiveLifetime.fieldWithTrace pointer).1 (encodeWithTrace rest).1
      have hLength : (BinaryPRGHeapPrimitiveLifetime.fieldWithTrace pointer).1.length = 2*pointer.length+1 := by
        rw [BinaryPRGHeapPrimitiveLifetime.fieldWithTrace_erasure,BinaryPRGWordStoreHeapMachine.fieldWithWork_erasure,field_length]
      rw [hLength] at hA
      have hw := wrap_usage 32 2 [(BinaryPRGHeapPrimitiveLifetime.fieldWithTrace pointer).2,(encodeWithTrace rest).2,
        (BinaryPRGHeapPrimitiveLifetime.appendWithTrace (BinaryPRGHeapPrimitiveLifetime.fieldWithTrace pointer).1 (encodeWithTrace rest).1).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (encodeWithTrace (pointer::rest)).2 ≤ _ at hw
      simp only [BinaryReferenceVector.payload,List.map_cons,List.sum_cons,List.length_cons] at *
      omega

theorem readField_allocation (tape : List Bool) :
    (BinaryPRGWordStoreHeapMachine.readFieldWithWork tape).2.allocatedBits ≤
      (BinaryPRGWordStoreHeapMachine.readFieldWithWork tape).2.work := by
  induction tape using BinaryPRGWordStoreHeapMachine.readFieldWithWork.induct with
  | case1 rest => simp [BinaryPRGWordStoreHeapMachine.readFieldWithWork]
  | case2 bit rest ih => simp only [BinaryPRGWordStoreHeapMachine.readFieldWithWork]; omega
  | case3 bits => cases bits <;> simp [BinaryPRGWordStoreHeapMachine.readFieldWithWork]

theorem readField_usage (tape : List Bool) :
    usage (BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace tape).2 ≤
      33*(BinaryPRGWordStoreHeapMachine.readFieldWithWork tape).2.work := by
  have h := BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace_bound tape
  have ha := readField_allocation tape
  unfold usage BinaryPRGHeapPrimitiveLifetime.price at *
  omega

theorem scan_usage (index : List Bool) : usage (BinaryBooleanPrimitiveLifetime.scanWithTrace index).2 ≤
    5*(BinaryStoredCountdown.nonzeroWithWork index).2 := by
  have h := BinaryBooleanPrimitiveLifetime.scanWithTrace_bounds index
  unfold usage cells BinaryStoredCountdown.nonzeroWithWork
  omega

theorem predecessor_usage (index : List Bool) :
    usage (BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace index).2 ≤
      4*(BinaryStoredCountdown.predecessorWithWork index).2 := by
  have hAll : ∀ index : List Bool,usage (BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace index).2 ≤
      16*BinaryStoredCountdown.predecessorVisits index := by
    intro index
    induction index with
    | nil => simp [BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace,usage,cells,listCells,arraySlots,framePeak,BinaryStoredCountdown.predecessorVisits]
    | cons bit rest ih =>
        cases bit
        · have ha := usage_append [.frames 1,.arrayAllocation 8,.listAllocation 1]
            (under 1 (BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace rest).2)
          have hu := usage_under 1 (BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace rest).2
          have hh : usage [.frames 1,.arrayAllocation 8,.listAllocation 1] = 10 := by simp [usage,cells,listCells,arraySlots,framePeak]
          rw [hh] at ha
          change usage (_++_) ≤ _
          simp only [BinaryStoredCountdown.predecessorVisits]
          omega
        · simp [BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace,usage,cells,listCells,arraySlots,framePeak,BinaryStoredCountdown.predecessorVisits]
  calc
    _ ≤ 16*BinaryStoredCountdown.predecessorVisits index := hAll index
    _ = 4*(BinaryStoredCountdown.predecessorWithWork index).2 := by
      simp only [BinaryStoredCountdown.predecessorWithWork]
      omega

def readWithTrace (tape index : List Bool) : Option Pointer × Trace :=
  let field := BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace tape
  match _hField : field.1 with
  | none => (none,wrap 16 2 [field.2])
  | some parsed =>
      let tested := BinaryBooleanPrimitiveLifetime.scanWithTrace index
      if tested.1 = true then
        let decremented := BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace index
        let later := readWithTrace parsed.2 decremented.1
        (later.1,wrap 48 2 [field.2,tested.2,decremented.2,later.2])
      else (some parsed.1,wrap 32 2 [field.2,tested.2])
termination_by tape.length
decreasing_by
  apply BinaryReferenceVector.readField_strict tape parsed
  change (BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace tape).1 = some parsed at _hField
  exact (BinaryPRGWordStoreHeapMachine.readFieldWithWork_erasure tape).symm.trans
    ((BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace_erasure tape).symm.trans _hField)

theorem read_state (tape index : List Bool) : (readWithTrace tape index).1 = (BinaryReferenceVector.readWithWork tape index).1 := by
  have hAll : ∀ length,∀ tape : List Bool,tape.length = length → ∀ index,
      (readWithTrace tape index).1 = (BinaryReferenceVector.readWithWork tape index).1 := by
    intro length
    induction length using Nat.strong_induction_on with
    | h length ih =>
        intro tape hLength index
        rw [readWithTrace,BinaryReferenceVector.readWithWork]
        dsimp only
        rw [BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace_erasure]
        cases hParsed : (BinaryPRGWordStoreHeapMachine.readFieldWithWork tape).1 with
        | none => simp only
        | some parsed =>
            simp only [BinaryBooleanPrimitiveLifetime.scanWithTrace_erases]
            have hLess := BinaryReferenceVector.readField_strict tape parsed
              ((BinaryPRGWordStoreHeapMachine.readFieldWithWork_erasure tape).symm.trans hParsed)
            by_cases hn : BinaryEuclideanGCD.nonzero index = true
            · simp only [ite_eq_left hn,BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure,
                BinaryStoredCountdown.predecessorWithWork_state]
              exact ih _ (by omega) parsed.2 rfl _
            · simp only [ite_eq_right hn]
  exact hAll _ tape rfl index

theorem read_usage (tape index : List Bool) : usage (readWithTrace tape index).2 ≤ 64*(BinaryReferenceVector.readWithWork tape index).2 := by
  have hAll : ∀ length,∀ tape : List Bool,tape.length = length → ∀ index,
      usage (readWithTrace tape index).2 ≤ 64*(BinaryReferenceVector.readWithWork tape index).2 := by
    intro length
    induction length using Nat.strong_induction_on with
    | h length ih =>
        intro tape hLength index
        have hf := readField_usage tape
        rw [readWithTrace,BinaryReferenceVector.readWithWork]
        dsimp only
        rw [BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace_erasure]
        cases hParsed : (BinaryPRGWordStoreHeapMachine.readFieldWithWork tape).1 with
        | none =>
            simp only
            have hw := wrap_usage 16 2 [(BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace tape).2]
            simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
            omega
        | some parsed =>
            simp only [BinaryBooleanPrimitiveLifetime.scanWithTrace_erases]
            have hLess := BinaryReferenceVector.readField_strict tape parsed
              ((BinaryPRGWordStoreHeapMachine.readFieldWithWork_erasure tape).symm.trans hParsed)
            have hs := scan_usage index
            by_cases hn : BinaryEuclideanGCD.nonzero index = true
            · simp only [ite_eq_left hn,BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure,
                BinaryStoredCountdown.predecessorWithWork_state]
              have hp := predecessor_usage index
              have hl := ih parsed.2.length (by omega) parsed.2 rfl (BinaryStoredCountdown.predecessor index)
              have hw := wrap_usage 48 2 [(BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace tape).2,
                (BinaryBooleanPrimitiveLifetime.scanWithTrace index).2,(BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace index).2,
                (readWithTrace parsed.2 (BinaryStoredCountdown.predecessor index)).2]
              simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
              unfold BinaryStoredCountdown.nonzeroWithWork at hs
              omega
            · simp only [ite_eq_right hn]
              have hw := wrap_usage 32 2 [(BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace tape).2,
                (BinaryBooleanPrimitiveLifetime.scanWithTrace index).2]
              simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
              unfold BinaryStoredCountdown.nonzeroWithWork at hs
              omega
  exact hAll _ tape rfl index

theorem read_all_prefix (tape index : List Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (readWithTrace tape index).2 steps ≤ borrowed+64*BinaryReferenceVector.readBound tape.length index.length ∧
      framePeak ((readWithTrace tape index).2.take steps) ≤ 64*BinaryReferenceVector.readBound tape.length index.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ ((read_usage tape index).trans (Nat.mul_le_mul_left 64 (BinaryReferenceVector.readWithWork_bound tape index))) borrowed steps

end Blotto.BinaryReferenceVectorLifetime
