import Blotto.BinaryArithmeticEntryWork
import Blotto.BinaryRegisterStoragePlan
import Blotto.BinaryPackedPairPlan

/-! Ghost arithmetic-entry visits follow the selected register producer and
its actual next state. Entry scans compose additively along every reached
instruction and are covered by existing retained-cell reservations. Observers
are proof-only and absent from selected execution; no runtime counter/field or
old price is changed. This is not the complete native/physical cost model. -/
namespace Blotto.BinaryRegisterArithmeticEntryWork
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryTracePlanMeasured
open BinaryPRGWordControllerPairRegisters
set_option autoImplicit false
set_option maxHeartbeats 5000000

def execute (instruction : Instruction) (registers : Registers) (depth : ℕ) : ℕ :=
  let left := BinaryRegisterTreePlan.lookupAt registers.tree instruction.left (depth+2)
  let right := BinaryRegisterTreePlan.lookupAt registers.tree instruction.right (depth+2)
  BinaryArithmeticEntryWork.raw instruction.op left.1.1 right.1.1

theorem execute_bound (instruction : Instruction) (registers : Registers) (depth : ℕ) :
    execute instruction registers depth ≤
      2*listCells (denote (BinaryRegisterStoragePlan.executeAt instruction registers depth).1.1.2) := by
  have h := BinaryArithmeticEntryWork.normalized_plan instruction.op
    (BinaryRegisterTreePlan.lookupAt registers.tree instruction.left (depth+2)).1.1
    (BinaryRegisterTreePlan.lookupAt registers.tree instruction.right (depth+2)).1.1 (depth+2)
  simp only [execute,BinaryRegisterStoragePlan.executeAt,denote,listCells_append,listCells]
  omega

def run : List Instruction → Registers → ℕ → ℕ
  | [],_registers,_depth => 0
  | instruction::rest,registers,depth =>
      let next := BinaryRegisterStoragePlan.executeAt instruction registers (depth+2)
      execute instruction registers (depth+2)+run rest next.1.1.1 (depth+1)

theorem run_bound (program : List Instruction) (registers : Registers) (depth : ℕ) :
    run program registers depth ≤
      2*listCells (denote (BinaryRegisterStoragePlan.runAt program registers depth).1.1.2) := by
  induction program generalizing registers depth with
  | nil => simp [run,BinaryRegisterStoragePlan.runAt,denote,listCells]
  | cons instruction rest ih =>
      have hn := execute_bound instruction registers (depth+2)
      have hl := ih (BinaryRegisterStoragePlan.executeAt instruction registers (depth+2)).1.1.1 (depth+1)
      simp only [run,BinaryRegisterStoragePlan.runAt,denote,listCells_append,listCells]
      omega

def pair (source : BinaryRationalPairProgram.Source) (depth : ℕ) : ℕ :=
  let init := BinaryRegisterTreePlan.initialAt source (depth+2)
  run code init.1.1 (depth+2)

theorem pair_bound (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    pair source depth ≤ 2*listCells (denote (BinaryRegisterStoragePlan.pairAt source depth).1.1.2) := by
  have h := run_bound code (BinaryRegisterTreePlan.initialAt source (depth+2)).1.1 (depth+2)
  simp only [pair,BinaryRegisterStoragePlan.pairAt,denote,listCells_append,listCells]
  omega

def outputs (source : BinaryRationalPairProgram.Source) (depth : ℕ) : ℕ := pair source (depth+2)

theorem outputs_bound (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    outputs source depth ≤ 2*listCells (denote (BinaryRegisterStoragePlan.outputsAt source depth).1.1.2) := by
  have h := pair_bound source (depth+2)
  simp only [outputs,BinaryRegisterStoragePlan.outputsAt,denote,listCells_append,listCells]
  omega

theorem emitted_bound (source : BinaryRationalPairProgram.Source) :
    outputs source 0 ≤ 2*listCells (BinaryRegisterStoragePlan.outputsWithEmission source).1.1.1.2 := by
  have h := outputs_bound source 0
  simpa only [BinaryRegisterStoragePlan.outputsWithEmission,BinaryNormalizationPlan.finishMeasured,
    BinaryNumericalReadbackPlan.finish,emitFull_erases,emit_data,List.append_nil] using h

theorem emitted_with_work (source : BinaryRationalPairProgram.Source) :
    let produced := (BinaryRegisterStoragePlan.outputsWithEmission source).1
    outputs source 0+produced.1.2+produced.2 ≤
      2*(listCells produced.1.1.2+produced.1.2+produced.2) := by
  have h := emitted_bound source
  dsimp only
  omega

theorem emitted_counter_width (source : BinaryRationalPairProgram.Source) :
    let produced := (BinaryRegisterStoragePlan.outputsWithEmission source).1
    binaryWordWidth (outputs source 0+produced.1.2+produced.2) ≤
      binaryWordWidth (2*(listCells produced.1.1.2+produced.1.2+produced.2)) :=
  binaryWordWidth_mono (emitted_with_work source)


open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryRationalEncoding (CanonicalWord)
variable {capacity : Store} {n : ℕ} {hCount : n=capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

theorem packed_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active=first::second::tail) :
    outputs (BinaryPackedPairPlan.source (hC := hC) limits state first second tail he).1.1.1 0 ≤
      2*listCells (BinaryPackedPairPlan.pairMeasured (hC := hC) limits state first second tail he).1.1.1.2 := by
  have h := emitted_bound (BinaryPackedPairPlan.source (hC := hC) limits state first second tail he).1.1.1
  simp only [BinaryPackedPairPlan.pairMeasured,BinaryWrapperEmission.two_trace,
    BinaryPRGHeapTraceUsage.wrap,BinaryPRGHeapTraceUsage.combine,listCells_append,listCells_under,listCells]
  omega

theorem packed_with_work (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active=first::second::tail) :
    let produced := (BinaryPackedPairPlan.pairMeasured (hC := hC) limits state first second tail he).1
    outputs (BinaryPackedPairPlan.source (hC := hC) limits state first second tail he).1.1.1 0+
      produced.1.2+produced.2 ≤ 2*(listCells produced.1.1.2+produced.1.2+produced.2) := by
  have h := packed_bound (hC := hC) limits state first second tail he
  dsimp only
  omega

end Blotto.BinaryRegisterArithmeticEntryWork
