import Blotto.BinaryRegisterCounterLayer
import Blotto.BinaryCompleteRepresentationSpace

/-! Source allocation/activation interpretation of the selected Boolean carry
counter. All allocated counter versions remain retained. The input word is
borrowed. Decoder buffers/scalars and native layout remain separate. -/
namespace Blotto.BinaryRegisterCounterSpace
open BinaryCarryCounter BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 2000000

def incrementTrace : List Bool → List Bool × Trace
  | [] => ([true],[.frames 1,.listAllocation 1])
  | false::rest => (true::rest,[.frames 1,.listAllocation 1])
  | true::rest =>
      let later := incrementTrace rest
      (false::later.1,[.frames 1,.listAllocation 1]++under 1 later.2)

theorem increment_state (counter : List Bool) : (incrementTrace counter).1 = increment counter := by
  induction counter with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [incrementTrace,increment,ih]

theorem increment_cells (counter : List Bool) : listCells (incrementTrace counter).2 = carryCells counter := by
  induction counter with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [incrementTrace,carryCells,listCells_append,listCells_under,listCells,ih,Nat.add_zero,Nat.add_comm]

theorem increment_arrays (counter : List Bool) : arraySlots (incrementTrace counter).2 = 0 ∧ arrayRecords (incrementTrace counter).2 = 0 := by
  induction counter with
  | nil => exact ⟨rfl,rfl⟩
  | cons bit rest ih => cases bit <;> simp only [incrementTrace,arraySlots_append,arrayRecords_append,arraySlots_under,arrayRecords_under,arraySlots,arrayRecords,ih.1,ih.2,Nat.add_zero,and_self]

theorem increment_frames (counter : List Bool) : framePeak (incrementTrace counter).2 ≤ counter.length+1 := by
  induction counter with
  | nil => simp [incrementTrace,framePeak]
  | cons bit rest ih => cases bit with
    | false => simp [incrementTrace,framePeak]
    | true =>
        have hu := framePeak_under 1 (incrementTrace rest).2
        simp only [incrementTrace,framePeak_append,framePeak,List.length_cons]
        omega

def countTrace : List Bool → List Bool → List Bool × Trace
  | [],counter => (counter,[.frames 1])
  | _::rest,counter =>
      let next := incrementTrace counter
      let later := countTrace rest next.1
      (later.1,[.frames 1]++under 1 next.2++under 1 later.2)

theorem count_state (word counter : List Bool) : (countTrace word counter).1 = count word counter := by
  induction word generalizing counter with
  | nil => rfl
  | cons bit rest ih => simp only [countTrace,count,ih,increment_state]

theorem count_cells (word counter : List Bool) : listCells (countTrace word counter).2 = countCarryCells word counter := by
  induction word generalizing counter with
  | nil => rfl
  | cons bit rest ih => simp only [countTrace,countCarryCells,listCells_append,listCells_under,listCells,ih,increment_state,increment_cells,Nat.zero_add]

theorem count_arrays (word counter : List Bool) : arraySlots (countTrace word counter).2 = 0 ∧ arrayRecords (countTrace word counter).2 = 0 := by
  induction word generalizing counter with
  | nil => exact ⟨rfl,rfl⟩
  | cons bit rest ih =>
      have hi := increment_arrays counter
      have hr := ih (incrementTrace counter).1
      simp only [countTrace,arraySlots_append,arrayRecords_append,arraySlots_under,arrayRecords_under,arraySlots,arrayRecords,hi.1,hi.2,hr.1,hr.2,Nat.zero_add,and_self]

theorem count_frames (word counter : List Bool) (Q : ℕ) (hCanonical : Canonical counter)
    (hValue : value counter+word.length ≤ Q) :
    framePeak (countTrace word counter).2 ≤ word.length+binaryWordWidth Q+3 := by
  induction word generalizing counter Q with
  | nil => simp [countTrace,framePeak]
  | cons bit rest ih =>
      have hNext : value (increment counter)+rest.length ≤ Q := by
        rw [value_increment]
        simp only [List.length_cons] at hValue
        omega
      have hr := ih (increment counter) Q (increment_canonical counter hCanonical) hNext
      have hWidth := (canonical_length_bound counter hCanonical).trans
        (binaryWordWidth_mono (show value counter ≤ Q by omega))
      have hf := increment_frames counter
      have hu := framePeak_under 1 (incrementTrace counter).2
      have hv := framePeak_under 1 (countTrace rest (increment counter)).2
      simp only [countTrace,increment_state,framePeak_append,framePeak,List.length_cons]
      omega

def owned (word : List Bool) : Trace := [.listAllocation 1]++(countTrace word [true]).2

theorem owned_cells (word : List Bool) : listCells (owned word) ≤ 2*word.length+2 := by
  have h := lengthFromOne_carry_bound word
  simp only [owned,listCells_append,listCells,count_cells]
  omega

theorem owned_arrays (word : List Bool) : arraySlots (owned word) = 0 ∧ arrayRecords (owned word) = 0 := by
  have h := count_arrays word [true]
  simp only [owned,arraySlots_append,arrayRecords_append,arraySlots,arrayRecords,h.1,h.2,and_self]

theorem owned_frames (word : List Bool) : framePeak (owned word) ≤ word.length+binaryWordWidth (word.length+1)+3 := by
  have h := count_frames word [true] (word.length+1) ⟨trivial,fun _ => rfl⟩ (by change 1+word.length ≤ word.length+1; omega)
  simpa only [owned,framePeak_append,framePeak,Nat.zero_max] using h

theorem owned_usage (word : List Bool) : usage (owned word)+arrayRecords (owned word) ≤ 7*(word.length+1) := by
  have hc := owned_cells word
  have hf := owned_frames word
  have ha := owned_arrays word
  have hl := Nat.log2_le_self (word.length+1)
  simp only [usage,BinaryPRGHeapPrimitiveLifetime.cells,ha.1,ha.2]
  unfold binaryWordWidth at hf
  omega

theorem every_prefix (prices : Representation) (word : List Bool) (steps : ℕ) :
    representedWorkspace prices (owned word) steps ≤ BinaryCompleteRepresentationSpace.units prices*(7*(word.length+1)) :=
  BinaryCompleteRepresentationSpace.represented_le prices (owned word) _ steps (owned_usage word)

theorem append_bound (first second : Trace) (A B : ℕ)
    (ha : usage first+arrayRecords first ≤ A) (hb : usage second+arrayRecords second ≤ B) :
    usage (first++second)+arrayRecords (first++second) ≤ A+B := by
  have h := usage_append first second
  rw [arrayRecords_append]
  omega

theorem price_pays_length (word : List Bool) : word.length+1 ≤ BinaryRegisterBooleanCount.sourcePrice word := by
  unfold BinaryRegisterBooleanCount.sourcePrice
  omega

open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerPairRegisters
open BinaryRegisterMetadataPlan
attribute [local irreducible] BinaryRegisterTreePlan.lookupAt BinaryNormalizationPlan.applyAt BinaryRegisterStoragePlan.executeAt BinaryRegisterStoragePlan.runAt

def wordTrace (word : SignedWord) : Trace := owned word.numerator++owned word.denominator

theorem word_bound (word : SignedWord) : usage (wordTrace word)+arrayRecords (wordTrace word) ≤ 7*counterPrice word := by
  have h := append_bound _ _ _ _ (owned_usage word.numerator) (owned_usage word.denominator)
  have hn := price_pays_length word.numerator
  have hd := price_pays_length word.denominator
  unfold wordTrace counterPrice
  omega

def executeTrace (instruction : Instruction) (registers : Registers) (depth : ℕ) : Trace :=
  let left := BinaryRegisterTreePlan.lookupAt registers.tree instruction.left (depth+2)
  let right := BinaryRegisterTreePlan.lookupAt registers.tree instruction.right (depth+2)
  let word := BinaryNormalizationPlan.applyAt instruction.op left.1.1 right.1.1 (depth+2)
  wordTrace left.1.1++wordTrace right.1.1++wordTrace word.1.1

theorem execute_bound (instruction : Instruction) (registers : Registers) (depth : ℕ) :
    usage (executeTrace instruction registers depth)+arrayRecords (executeTrace instruction registers depth) ≤
      7*BinaryRegisterCounterLayer.execute instruction registers depth := by
  have hl := word_bound (BinaryRegisterTreePlan.lookupAt registers.tree instruction.left (depth+2)).1.1
  have hr := word_bound (BinaryRegisterTreePlan.lookupAt registers.tree instruction.right (depth+2)).1.1
  have hw := word_bound (BinaryNormalizationPlan.applyAt instruction.op
    (BinaryRegisterTreePlan.lookupAt registers.tree instruction.left (depth+2)).1.1
    (BinaryRegisterTreePlan.lookupAt registers.tree instruction.right (depth+2)).1.1 (depth+2)).1.1
  have h := append_bound _ _ _ _ (append_bound _ _ _ _ hl hr) hw
  simpa only [executeTrace,BinaryRegisterCounterLayer.execute,Nat.mul_add] using h

def runTrace : List Instruction → Registers → ℕ → Trace
  | [],_,_ => []
  | instruction::rest,registers,depth =>
      let next := BinaryRegisterStoragePlan.executeAt instruction registers (depth+2)
      executeTrace instruction registers (depth+2)++runTrace rest next.1.1.1 (depth+1)

theorem run_bound (program : List Instruction) (registers : Registers) (depth : ℕ) :
    usage (runTrace program registers depth)+arrayRecords (runTrace program registers depth) ≤
      7*BinaryRegisterCounterLayer.run program registers depth := by
  induction program generalizing registers depth with
  | nil => simp [runTrace,BinaryRegisterCounterLayer.run,usage,BinaryPRGHeapPrimitiveLifetime.cells,listCells,arraySlots,framePeak,arrayRecords]
  | cons instruction rest ih =>
      have he := execute_bound instruction registers (depth+2)
      have hr := ih (BinaryRegisterStoragePlan.executeAt instruction registers (depth+2)).1.1.1 (depth+1)
      simpa only [runTrace,BinaryRegisterCounterLayer.run,Nat.mul_add] using append_bound _ _ _ _ he hr

theorem every_program_prefix (prices : Representation) (program : List Instruction)
    (registers : Registers) (depth used steps : ℕ) :
    representedWorkspace prices (runTrace (program.take used) registers depth) steps ≤
      BinaryCompleteRepresentationSpace.units prices*(5264*(BinaryRegisterStoragePlan.runAt program registers depth).1.2.1) := by
  apply BinaryCompleteRepresentationSpace.represented_le
  have ht := run_bound (program.take used) registers depth
  have hp := Nat.mul_le_mul_left 7 (BinaryRegisterCounterLayer.every_prefix program registers depth used)
  simpa only [← Nat.mul_assoc,Nat.reduceMul] using ht.trans hp

def copiedTrace : {height : ℕ} → Tree height → Trace
  | _,.leaf word => wordTrace word
  | _,.branch left right => copiedTrace left++copiedTrace right

theorem copied_bound {height : ℕ} (tree : Tree height) :
    usage (copiedTrace tree)+arrayRecords (copiedTrace tree) ≤ 7*copiedCounterPrice tree := by
  induction tree with
  | leaf word => exact word_bound word
  | branch left right hl hr => simpa only [copiedTrace,copiedCounterPrice,Nat.mul_add] using append_bound _ _ _ _ hl hr

def pairTrace (source : BinaryRationalPairProgram.Source) (depth : ℕ) : Trace :=
  let init := BinaryRegisterTreePlan.initialAt source (depth+2)
  runTrace code init.1.1 (depth+2)++copiedTrace init.1.1.tree

theorem pair_bound (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    usage (pairTrace source depth)+arrayRecords (pairTrace source depth) ≤ 7*BinaryRegisterCounterLayer.pair source depth := by
  have hi := copied_bound (BinaryRegisterTreePlan.initialAt source (depth+2)).1.1.tree
  have hr := run_bound code (BinaryRegisterTreePlan.initialAt source (depth+2)).1.1 (depth+2)
  simpa only [pairTrace,BinaryRegisterCounterLayer.pair,Nat.mul_add,Nat.add_comm] using append_bound _ _ _ _ hr hi

def outputsTrace (source : BinaryRationalPairProgram.Source) (depth : ℕ) : Trace :=
  let registers := BinaryRegisterStoragePlan.pairAt source (depth+2)
  let lower := BinaryRegisterTreePlan.lookupAt registers.1.1.1.tree a7 (depth+2)
  let upper := BinaryRegisterTreePlan.lookupAt registers.1.1.1.tree a8 (depth+2)
  let probability := BinaryRegisterTreePlan.lookupAt registers.1.1.1.tree a11 (depth+2)
  pairTrace source (depth+2)++wordTrace lower.1.1++wordTrace upper.1.1++wordTrace probability.1.1

theorem outputs_bound (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    usage (outputsTrace source depth)+arrayRecords (outputsTrace source depth) ≤ 7*BinaryRegisterCounterLayer.outputs source depth := by
  have hp := pair_bound source (depth+2)
  have hl := word_bound (BinaryRegisterTreePlan.lookupAt (BinaryRegisterStoragePlan.pairAt source (depth+2)).1.1.1.tree a7 (depth+2)).1.1
  have hu := word_bound (BinaryRegisterTreePlan.lookupAt (BinaryRegisterStoragePlan.pairAt source (depth+2)).1.1.1.tree a8 (depth+2)).1.1
  have hb := word_bound (BinaryRegisterTreePlan.lookupAt (BinaryRegisterStoragePlan.pairAt source (depth+2)).1.1.1.tree a11 (depth+2)).1.1
  simpa only [outputsTrace,BinaryRegisterCounterLayer.outputs,Nat.mul_add] using
    append_bound _ _ _ _ (append_bound _ _ _ _ (append_bound _ _ _ _ hp hl) hu) hb

def inputTrace (source : BinaryRationalPairProgram.Source) : Trace :=
  wordTrace source.lengthI++wordTrace source.lengthJ++wordTrace source.resourceI++wordTrace source.resourceJ

theorem input_bound (source : BinaryRationalPairProgram.Source) :
    usage (inputTrace source)+arrayRecords (inputTrace source) ≤ 7*sourceCounterPrice source := by
  have ha := word_bound source.lengthI
  have hb := word_bound source.lengthJ
  have hc := word_bound source.resourceI
  have hd := word_bound source.resourceJ
  simpa only [inputTrace,sourceCounterPrice,Nat.mul_add] using
    append_bound _ _ _ _ (append_bound _ _ _ _ (append_bound _ _ _ _ ha hb) hc) hd

open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap, CanonicalWord (lookup capacity.tree address.word)}

def packedTrace (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) : Trace :=
  let input := (BinaryPackedPairPlan.source (hC := hC) limits state first second tail he).1
  outputsTrace input.1.1 0++inputTrace input.1.1

theorem packed_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    usage (packedTrace (hC := hC) limits state first second tail he)+arrayRecords (packedTrace (hC := hC) limits state first second tail he) ≤
      7*BinaryRegisterCounterLayer.packed (hC := hC) limits state first second tail he := by
  have hi := input_bound (BinaryPackedPairPlan.source (hC := hC) limits state first second tail he).1.1.1
  have ho := outputs_bound (BinaryPackedPairPlan.source (hC := hC) limits state first second tail he).1.1.1 0
  simpa only [packedTrace,BinaryRegisterCounterLayer.packed,Nat.mul_add,Nat.add_comm] using append_bound _ _ _ _ ho hi

theorem every_packed_prefix (prices : Representation) (limits : Stored capacity.tree)
    (state : Finished capacity n hCount) (first second : Address capacity.width capacity.cap)
    (tail : List (Address capacity.width capacity.cap)) (he : state.active = first::second::tail) (steps : ℕ) :
    representedWorkspace prices (packedTrace (hC := hC) limits state first second tail he) steps ≤
      BinaryCompleteRepresentationSpace.units prices*(5264*(BinaryPackedPairPlan.pairMeasured (hC := hC) limits state first second tail he).1.1.2) := by
  apply BinaryCompleteRepresentationSpace.represented_le
  have ht := packed_bound (hC := hC) limits state first second tail he
  have hp := Nat.mul_le_mul_left 7 (BinaryRegisterCounterLayer.packed_bound (hC := hC) limits state first second tail he)
  simpa only [← Nat.mul_assoc,Nat.reduceMul] using ht.trans hp

end Blotto.BinaryRegisterCounterSpace
