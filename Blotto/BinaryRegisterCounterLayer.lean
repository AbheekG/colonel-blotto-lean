import Blotto.BinaryPackedPairPlan

/-! Counter prices follow actual instruction operands and actual returned
register states. These observers are not called by the executable producer.
The fixed decoder interpretation and native-calibration boundary are retained. -/
namespace Blotto.BinaryRegisterCounterLayer
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerPairRegisters
open BinaryRegisterMetadataPlan
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local irreducible] BinaryRegisterTreePlan.lookupAt BinaryRegisterTreePlan.writeAt BinaryRegisterTreePlan.initialAt BinaryNormalizationPlan.applyAt BinaryRegisterMetadataPlan.cursorAt BinaryRegisterStoragePlan.executeAt BinaryRegisterStoragePlan.runAt BinaryRegisterStoragePlan.pairAt BinaryRegisterStoragePlan.outputsAt

def execute (instruction : Instruction) (registers : Registers) (depth : ℕ) : ℕ :=
  let left := BinaryRegisterTreePlan.lookupAt registers.tree instruction.left (depth+2)
  let right := BinaryRegisterTreePlan.lookupAt registers.tree instruction.right (depth+2)
  let word := BinaryNormalizationPlan.applyAt instruction.op left.1.1 right.1.1 (depth+2)
  counterPrice left.1.1+counterPrice right.1.1+counterPrice word.1.1

theorem execute_bound (instruction : Instruction) (registers : Registers) (depth : ℕ) :
    execute instruction registers depth ≤ 752*(BinaryRegisterStoragePlan.executeAt instruction registers depth).1.2.1 := by
  have hl := counter_read (BinaryRegisterTreePlan.lookupAt registers.tree instruction.left (depth+2)).1.1
  have hr := counter_read (BinaryRegisterTreePlan.lookupAt registers.tree instruction.right (depth+2)).1.1
  have hw := counter_write (BinaryNormalizationPlan.applyAt instruction.op
    (BinaryRegisterTreePlan.lookupAt registers.tree instruction.left (depth+2)).1.1
    (BinaryRegisterTreePlan.lookupAt registers.tree instruction.right (depth+2)).1.1 (depth+2)).1.1
  simp only [execute,BinaryRegisterStoragePlan.executeAt]
  omega

def run : List Instruction → Registers → ℕ → ℕ
  | [],_,_ => 0
  | instruction::rest,registers,depth =>
      let next := BinaryRegisterStoragePlan.executeAt instruction registers (depth+2)
      execute instruction registers (depth+2)+run rest next.1.1.1 (depth+1)

theorem run_bound (program : List Instruction) (registers : Registers) (depth : ℕ) :
    run program registers depth ≤ 752*(BinaryRegisterStoragePlan.runAt program registers depth).1.2.1 := by
  induction program generalizing registers depth with
  | nil => simp only [run,BinaryRegisterStoragePlan.runAt]; omega
  | cons instruction rest ih =>
      have he := execute_bound instruction registers (depth+2)
      have hr := ih (BinaryRegisterStoragePlan.executeAt instruction registers (depth+2)).1.1.1 (depth+1)
      simp only [run,BinaryRegisterStoragePlan.runAt]
      omega

theorem prefix_le (program : List Instruction) (registers : Registers) (depth used : ℕ) :
    run (program.take used) registers depth ≤ run program registers depth := by
  induction program generalizing registers depth used with
  | nil => simp only [List.take_nil,run]; omega
  | cons instruction rest ih => cases used with
    | zero => simp only [List.take_zero,run]; omega
    | succ used =>
        have h := ih (BinaryRegisterStoragePlan.executeAt instruction registers (depth+2)).1.1.1 (depth+1) used
        simpa only [List.take_succ_cons,run] using Nat.add_le_add_left h (execute instruction registers (depth+2))

theorem every_prefix (program : List Instruction) (registers : Registers) (depth used : ℕ) :
    run (program.take used) registers depth ≤ 752*(BinaryRegisterStoragePlan.runAt program registers depth).1.2.1 :=
  (prefix_le program registers depth used).trans (run_bound program registers depth)

def pair (source : BinaryRationalPairProgram.Source) (depth : ℕ) : ℕ :=
  let init := BinaryRegisterTreePlan.initialAt source (depth+2)
  copiedCounterPrice init.1.1.tree+run code init.1.1 (depth+2)

theorem pair_bound (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    pair source depth ≤ 752*(BinaryRegisterStoragePlan.pairAt source depth).1.2.1 := by
  have hi := counter_initial (BinaryRegisterTreePlan.initialAt source (depth+2)).1.1.tree
  have hr := run_bound code (BinaryRegisterTreePlan.initialAt source (depth+2)).1.1 (depth+2)
  simp only [pair,BinaryRegisterStoragePlan.pairAt]
  omega

def outputs (source : BinaryRationalPairProgram.Source) (depth : ℕ) : ℕ :=
  let registers := BinaryRegisterStoragePlan.pairAt source (depth+2)
  let lower := BinaryRegisterTreePlan.lookupAt registers.1.1.1.tree a7 (depth+2)
  let upper := BinaryRegisterTreePlan.lookupAt registers.1.1.1.tree a8 (depth+2)
  let probability := BinaryRegisterTreePlan.lookupAt registers.1.1.1.tree a11 (depth+2)
  pair source (depth+2)+counterPrice lower.1.1+counterPrice upper.1.1+counterPrice probability.1.1

theorem outputs_bound (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    outputs source depth ≤ 752*(BinaryRegisterStoragePlan.outputsAt source depth).1.2.1 := by
  have hp := pair_bound source (depth+2)
  have hl := counter_read (BinaryRegisterTreePlan.lookupAt
    (BinaryRegisterStoragePlan.pairAt source (depth+2)).1.1.1.tree a7 (depth+2)).1.1
  have hu := counter_read (BinaryRegisterTreePlan.lookupAt
    (BinaryRegisterStoragePlan.pairAt source (depth+2)).1.1.1.tree a8 (depth+2)).1.1
  have hb := counter_read (BinaryRegisterTreePlan.lookupAt
    (BinaryRegisterStoragePlan.pairAt source (depth+2)).1.1.1.tree a11 (depth+2)).1.1
  simp only [outputs,BinaryRegisterStoragePlan.outputsAt]
  omega

theorem emitted_bound (source : BinaryRationalPairProgram.Source) :
    outputs source 0 ≤ 752*(BinaryRegisterStoragePlan.outputsWithEmission source).1.1.2 := by
  simpa only [BinaryRegisterStoragePlan.outputsWithEmission,BinaryNormalizationPlan.finishMeasured,
    BinaryNumericalReadbackPlan.finish] using outputs_bound source 0

open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,
  CanonicalWord (lookup capacity.tree address.word)}

def packed (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) : ℕ :=
  let input := (BinaryPackedPairPlan.source (hC := hC) limits state first second tail he).1
  sourceCounterPrice input.1.1+outputs input.1.1 0

theorem packed_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    packed (hC := hC) limits state first second tail he ≤
      752*(BinaryPackedPairPlan.pairMeasured (hC := hC) limits state first second tail he).1.1.2 := by
  have hs := counter_source (BinaryPackedPairPlan.source (hC := hC) limits state first second tail he).1.1.1
  have ho := emitted_bound (BinaryPackedPairPlan.source (hC := hC) limits state first second tail he).1.1.1
  simp only [packed,BinaryPackedPairPlan.pairMeasured]
  omega

end Blotto.BinaryRegisterCounterLayer
