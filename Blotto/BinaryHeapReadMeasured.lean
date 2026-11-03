import Blotto.BinaryHeapTapeMeasured
import Blotto.BooleanFreshSeedMeasured
import Blotto.BinarySeedTraceBounds

/-! Selected physical heap reads consume the actual parsed fields, Boolean
scan and predecessor results once. Their data/traces and charges agree with
the existing source models. Scan charges reserve the complete pointer width;
they are not claims about native length/observer evaluation or references. -/

namespace Blotto.BinaryHeapReadMeasured
open BinaryRationalNormalization BinaryPRGWordStoreHeap BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryTraceDepth
open BinaryPRGWordStoreHeapMachine (Charge)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def decodeAt : List Bool → ℕ → (Option Cell × Trace) × Charge
  | false::negative::rest,depth =>
      let first := BinaryHeapTapeMeasured.readFieldAt rest (depth+1)
      match first.1.1 with
      | none => ((none,.frames (depth+2)::.arrayAllocation 8::first.1.2),
          ⟨first.2.work+4,first.2.allocatedBits+4⟩)
      | some parsed =>
          let second := BinaryHeapTapeMeasured.readFieldAt parsed.2 (depth+1)
          ((second.1.1.map (fun later => .leaf ⟨negative,parsed.1,later.1⟩),
            .frames (depth+2)::.arrayAllocation 16::(first.1.2++second.1.2)),
            ⟨first.2.work+second.2.work+6,first.2.allocatedBits+second.2.allocatedBits+4⟩)
  | true::rest,depth =>
      let first := BinaryHeapTapeMeasured.readFieldAt rest (depth+1)
      match first.1.1 with
      | none => ((none,.frames (depth+2)::.arrayAllocation 8::first.1.2),
          ⟨first.2.work+3,first.2.allocatedBits+4⟩)
      | some parsed =>
          let second := BinaryHeapTapeMeasured.readFieldAt parsed.2 (depth+1)
          ((second.1.1.map (fun later => .branch parsed.1 later.1),
            .frames (depth+2)::.arrayAllocation 16::(first.1.2++second.1.2)),
            ⟨first.2.work+second.2.work+5,first.2.allocatedBits+second.2.allocatedBits+4⟩)
  | _,depth => ((none,[.frames (depth+1),.arrayAllocation 8]),⟨2,0⟩)


theorem decodeAt_erases (bits : List Bool) (depth : ℕ) :
    (decodeAt bits depth).1 = ((BinaryPRGHeapAllocationLifetime.decodeWithTrace bits).1,
      under depth (BinaryPRGHeapAllocationLifetime.decodeWithTrace bits).2) := by
  cases bits with
  | nil => rfl
  | cons tag rest => cases tag with
    | false => cases rest with
      | nil => rfl
      | cons negative rest =>
          simp only [decodeAt,BinaryPRGHeapAllocationLifetime.decodeWithTrace,
            BinaryHeapTapeMeasured.readFieldAt_erases]
          split <;> rename_i hParsed <;> simp only [hParsed,under_append,under_compose,List.append_assoc] <;> rfl
    | true =>
        simp only [decodeAt,BinaryPRGHeapAllocationLifetime.decodeWithTrace,
          BinaryHeapTapeMeasured.readFieldAt_erases]
        split <;> rename_i hParsed <;> simp only [hParsed,under_append,under_compose,List.append_assoc] <;> rfl

def decode (bits : List Bool) : (Option Cell × Trace) × Charge := decodeAt bits 0

theorem decode_erases (bits : List Bool) :
    (decode bits).1 = BinaryPRGHeapAllocationLifetime.decodeWithTrace bits := by
  rw [decode,decodeAt_erases,under_zero]

theorem decode_data (bits : List Bool) :
    (decode bits).1.1 = (BinaryPRGWordStoreHeapMachine.decodeWithWork bits).1 := by
  have h := congrArg Prod.fst (decode_erases bits)
  exact h.trans (BinaryPRGHeapAllocationLifetime.decodeWithTrace_erasure bits)

theorem decodeAt_charge (bits : List Bool) (depth : ℕ) :
    (decodeAt bits depth).2 = (BinaryPRGWordStoreHeapMachine.decodeWithWork bits).2 := by
  cases bits with
  | nil => rfl
  | cons tag rest => cases tag with
    | false => cases rest with
      | nil => rfl
      | cons negative rest =>
          simp only [decodeAt,BinaryPRGWordStoreHeapMachine.decodeWithWork,
            BinaryHeapTapeMeasured.readFieldAt_erases,
            BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace_erasure,BinaryHeapTapeMeasured.readFieldAt_charge]
          split <;> rename_i hParsed <;> simp only [hParsed]
    | true =>
        simp only [decodeAt,BinaryPRGWordStoreHeapMachine.decodeWithWork,
          BinaryHeapTapeMeasured.readFieldAt_erases,
            BinaryPRGHeapPrimitiveLifetime.readFieldWithTrace_erasure,BinaryHeapTapeMeasured.readFieldAt_charge]
        split <;> rename_i hParsed <;> simp only [hParsed]


theorem decode_charge (bits : List Bool) :
    (decode bits).2 = (BinaryPRGWordStoreHeapMachine.decodeWithWork bits).2 := decodeAt_charge bits 0

-- Width is cached once by the public entry. Depth changes only event frames.
def skipAt (tape : List Bool) (pointer : Pointer) (width depth : ℕ) :
    (List Bool × Trace) × Charge :=
  let tested := BooleanFreshSeedMeasured.scanAt pointer (depth+1)
  if tested.1.1 then
    match tape with
    | [] => (([],.frames (depth+2)::.arrayAllocation 8::tested.1.2),⟨width+1+1,0⟩)
    | _::rest =>
        let decremented := BooleanFreshSeedMeasured.predecessorAt pointer (depth+1)
        let later := skipAt rest decremented.1.1 width (depth+1)
        ((later.1.1,.frames (depth+2)::.arrayAllocation 8::
          (tested.1.2++(decremented.1.2++later.1.2))),
          ⟨width+1+decremented.2+later.2.work+3,width+later.2.allocatedBits⟩)
  else ((tape,.frames (depth+2)::.arrayAllocation 8::tested.1.2),⟨width+1+1,0⟩)
termination_by tape.length

theorem skipAt_erases (tape : List Bool) (pointer : Pointer) (width depth : ℕ) :
    (skipAt tape pointer width depth).1 =
      ((BinaryPRGHeapPrimitiveLifetime.skipWithTrace tape pointer).1,
        under depth (BinaryPRGHeapPrimitiveLifetime.skipWithTrace tape pointer).2) := by
  induction tape generalizing pointer width depth with
  | nil =>
      rw [skipAt,BinaryPRGHeapPrimitiveLifetime.skipWithTrace]
      simp only [BooleanFreshSeedMeasured.scanAt_erases]
      split <;> simp only [under_append,under_compose] <;> rfl
  | cons bit rest ih =>
      rw [skipAt,BinaryPRGHeapPrimitiveLifetime.skipWithTrace]
      dsimp only
      simp only [BooleanFreshSeedMeasured.scanAt_erases]
      split
      · simp only [BooleanFreshSeedMeasured.predecessorAt_erases,ih,under_append,under_compose,List.append_assoc]
        rfl
      · simp only [under_append,under_compose]
        rfl

def skip (tape : List Bool) (pointer : Pointer) : (List Bool × Trace) × Charge :=
  skipAt tape pointer pointer.length 0

theorem skip_erases (tape : List Bool) (pointer : Pointer) :
    (skip tape pointer).1 = BinaryPRGHeapPrimitiveLifetime.skipWithTrace tape pointer := by
  rw [skip,skipAt_erases,under_zero]

theorem skip_data (tape : List Bool) (pointer : Pointer) :
    (skip tape pointer).1.1 = (BinaryPRGWordStoreHeapMachine.skipWithWork tape pointer).1 := by
  have h := congrArg Prod.fst (skip_erases tape pointer)
  exact h.trans (BinaryPRGHeapPrimitiveLifetime.skipWithTrace_erasure tape pointer)

theorem skipAt_charge (tape : List Bool) (pointer : Pointer) (width depth : ℕ)
    (hWidth : pointer.length = width) :
    (skipAt tape pointer width depth).2 =
      (BinaryPRGWordStoreHeapMachine.skipWithWork tape pointer).2 := by
  induction tape generalizing pointer width depth with
  | nil =>
      rw [skipAt,BinaryPRGWordStoreHeapMachine.skipWithWork]
      simp only [BooleanFreshSeedMeasured.scanAt_erases,
        BinaryBooleanPrimitiveLifetime.scanWithTrace_erases,BinaryStoredCountdown.nonzeroWithWork]
      split <;> rename_i hn <;> simp only [hn,Bool.false_eq_true,ite_true,ite_false,hWidth]
  | cons bit rest ih =>
      rw [skipAt,BinaryPRGWordStoreHeapMachine.skipWithWork]
      simp only [BooleanFreshSeedMeasured.scanAt_erases,
        BinaryBooleanPrimitiveLifetime.scanWithTrace_erases,BinaryStoredCountdown.nonzeroWithWork]
      split
      · rename_i hn
        have hpWidth : (BinaryStoredCountdown.predecessor pointer).length = width := by
          rw [BinaryStoredCountdown.predecessor_length,hWidth]
        simp only [BooleanFreshSeedMeasured.predecessorAt_erases,
          BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure,
          BooleanFreshSeedMeasured.predecessorAt_work,
          BinaryStoredCountdown.predecessorWithWork_state]
        rw [ih _ width (depth+1) hpWidth]
        simp only [BinaryStoredCountdown.predecessorWithWork,hWidth,hn,ite_true]
      · rename_i hn
        simp only [hn,Bool.false_eq_true,ite_true,ite_false,hWidth]

theorem skip_charge (tape : List Bool) (pointer : Pointer) :
    (skip tape pointer).2 = (BinaryPRGWordStoreHeapMachine.skipWithWork tape pointer).2 :=
  skipAt_charge tape pointer pointer.length 0 rfl

def readAt (tape : List Bool) (pointer : Pointer) (depth : ℕ) : (Option Cell × Trace) × Charge :=
  let reached := skipAt tape pointer pointer.length (depth+1)
  let parsed := decodeAt reached.1.1 (depth+1)
  ((parsed.1.1,.frames (depth+2)::.arrayAllocation 8::(reached.1.2++parsed.1.2)),
    reached.2.add parsed.2)

theorem readAt_erases (tape : List Bool) (pointer : Pointer) (depth : ℕ) :
    (readAt tape pointer depth).1 = ((BinaryPRGHeapAllocationLifetime.readWithTrace tape pointer).1,
      under depth (BinaryPRGHeapAllocationLifetime.readWithTrace tape pointer).2) := by
  simp only [readAt,BinaryPRGHeapAllocationLifetime.readWithTrace,skipAt_erases,
    decodeAt_erases,under_append,under_compose,List.append_assoc]
  rfl

def read (tape : List Bool) (pointer : Pointer) : (Option Cell × Trace) × Charge := readAt tape pointer 0

theorem read_erases (tape : List Bool) (pointer : Pointer) :
    (read tape pointer).1 = BinaryPRGHeapAllocationLifetime.readWithTrace tape pointer := by
  rw [read,readAt_erases,under_zero]

theorem read_data (tape : List Bool) (pointer : Pointer) :
    (read tape pointer).1.1 = (BinaryPRGWordStoreHeapMachine.readWithWork tape pointer).1 := by
  have h := congrArg Prod.fst (read_erases tape pointer)
  exact h.trans (BinaryPRGHeapAllocationLifetime.readWithTrace_erasure tape pointer)

theorem readAt_charge (tape : List Bool) (pointer : Pointer) (depth : ℕ) :
    (readAt tape pointer depth).2 = (BinaryPRGWordStoreHeapMachine.readWithWork tape pointer).2 := by
  have hs := skipAt_charge tape pointer pointer.length (depth+1) rfl
  simp only [readAt,BinaryPRGWordStoreHeapMachine.readWithWork,hs,skipAt_erases,
    BinaryPRGHeapPrimitiveLifetime.skipWithTrace_erasure,decodeAt_charge]

theorem read_charge (tape : List Bool) (pointer : Pointer) :
    (read tape pointer).2 = (BinaryPRGWordStoreHeapMachine.readWithWork tape pointer).2 := readAt_charge tape pointer 0

theorem read_bound (tape : List Bool) (pointer : Pointer) :
    (read tape pointer).2.work ≤ BinaryPRGWordStoreHeapMachine.readBound tape.length pointer.length ∧
      (read tape pointer).2.allocatedBits ≤ tape.length*pointer.length+2*tape.length+4 := by
  rw [read_charge]
  exact BinaryPRGWordStoreHeapMachine.readWithWork_bounds tape pointer

theorem read_all_prefix (tape : List Bool) (pointer : Pointer) (borrowed steps : ℕ) :
    retainedHeap borrowed (read tape pointer).1.2 steps ≤
        borrowed+32*((read tape pointer).2.work+(read tape pointer).2.allocatedBits+1) ∧
      framePeak ((read tape pointer).1.2.take steps) ≤
        32*((read tape pointer).2.work+(read tape pointer).2.allocatedBits+1) := by
  rw [read_erases,read_charge]
  apply all_prefix
  have h := BinaryPRGHeapAllocationLifetime.readWithTrace_bound tape pointer
  unfold usage BinaryPRGHeapPrimitiveLifetime.price at *
  omega

theorem skipAt_observers (tape : List Bool) (pointer : Pointer) (width depth : ℕ)
    (hWidth : pointer.length = width) :
    (skipAt tape pointer width depth).1.2.length ≤ 2*(skipAt tape pointer width depth).2.work ∧
      framePeak (skipAt tape pointer width depth).1.2 ≤ depth+tape.length+width+2 := by
  induction tape generalizing pointer width depth with
  | nil =>
      have hs := BooleanFreshSeedMeasured.scanAt_trace_length pointer (depth+1)
      have hf := BooleanFreshSeedMeasured.scanAt_frames pointer (depth+1)
      rw [skipAt]
      split <;> constructor
      all_goals
        simp only [List.length_cons,List.length_nil,framePeak]
        omega
  | cons bit rest ih =>
      have hs := BooleanFreshSeedMeasured.scanAt_trace_length pointer (depth+1)
      have hf := BooleanFreshSeedMeasured.scanAt_frames pointer (depth+1)
      rw [skipAt]
      dsimp only
      split
      · have hData : (BooleanFreshSeedMeasured.predecessorAt pointer (depth+1)).1.1 =
            BinaryStoredCountdown.predecessor pointer := by
          rw [BooleanFreshSeedMeasured.predecessorAt_erases,
            BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure]
        have hpWidth : (BinaryStoredCountdown.predecessor pointer).length = width := by
          rw [BinaryStoredCountdown.predecessor_length,hWidth]
        have hl := ih (BinaryStoredCountdown.predecessor pointer) width (depth+1) hpWidth
        have hp := BinarySeedTraceBounds.predecessor_trace_work pointer (depth+1)
        have hpf := BooleanFreshSeedMeasured.predecessorAt_frames pointer (depth+1)
        rw [hData]
        constructor
        · simp only [List.length_cons,List.length_append]
          omega
        · simp only [List.length_cons,framePeak,framePeak_append]
          omega
      · constructor
        · simp only [List.length_cons,List.length_nil]
          omega
        · simp only [List.length_cons,framePeak]
          omega

theorem skipAt_frame_width (tape : List Bool) (pointer : Pointer) (width depth count : ℕ)
    (hWidth : pointer.length = width) (h : .frames count ∈ (skipAt tape pointer width depth).1.2) :
    binaryWordWidth count ≤
      binaryWordWidth (depth+tape.length+width+2) :=
  binaryWordWidth_mono
    ((BinarySeedTraceBounds.frames_le_peak _ count h).trans
      (skipAt_observers tape pointer width depth hWidth).2)

theorem decodeAt_trace_work (bits : List Bool) (depth : ℕ) :
    (decodeAt bits depth).1.2.length ≤ 2*(decodeAt bits depth).2.work := by
  cases bits with
  | nil => simp [decodeAt]
  | cons tag rest => cases tag with
    | false => cases rest with
      | nil => simp [decodeAt]
      | cons negative rest =>
          have hFirst := (BinaryHeapTapeMeasured.readFieldAt_observers rest (depth+1)).1
          simp only [decodeAt]
          split
          · simp only [List.length_cons,List.length_nil]; omega
          · rename_i parsed hParsed
            have hSecond := (BinaryHeapTapeMeasured.readFieldAt_observers parsed.2 (depth+1)).1
            simp only [List.length_cons,List.length_append,List.length_nil]
            omega
    | true =>
        have hFirst := (BinaryHeapTapeMeasured.readFieldAt_observers rest (depth+1)).1
        simp only [decodeAt]
        split
        · simp only [List.length_cons,List.length_nil]; omega
        · rename_i parsed hParsed
          have hSecond := (BinaryHeapTapeMeasured.readFieldAt_observers parsed.2 (depth+1)).1
          simp only [List.length_cons,List.length_append,List.length_nil]
          omega

theorem readAt_trace_work (tape : List Bool) (pointer : Pointer) (depth : ℕ) :
    (readAt tape pointer depth).1.2.length ≤ 2*((readAt tape pointer depth).2.work+1) := by
  have hs := (skipAt_observers tape pointer pointer.length (depth+1) rfl).1
  have hd := decodeAt_trace_work (skipAt tape pointer pointer.length (depth+1)).1.1 (depth+1)
  simp only [readAt,Charge.add,List.length_cons,List.length_append]
  omega

end Blotto.BinaryHeapReadMeasured
