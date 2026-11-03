import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryQuadraticResourcePairLifetime
import Blotto.BinaryQuadraticMeasured
import Blotto.BinaryHeapEnumerationMeasured

/-! The reached seven-instruction pair program returns its old register
values, trace and source charge with the actual opcode division-work total.
Read/write payload charges use words actually returned by the execution;
no second opcode/register program runs for either work ledger.
Native metadata, trace evaluation and reference/allocator costs remain separate. -/
namespace Blotto.BinaryHeapPairRegistersMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerPairRegisters
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 3000000

def executeMeasured (instruction : Instruction) (registers : Registers) : ((Registers × Trace) × ℕ) × ℕ :=
  let left := BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.left
  let right := BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.right
  let word := BinaryPlannedQuadratic.applyMeasured instruction.op left.1 right.1
  let written := BinaryQuadraticResourcePairLifetime.writeWithTrace registers.tree registers.cursor word.1.1.1
  let advanced := BinaryHeapEnumerationMeasured.advance registers.cursor
  (((⟨written.1,advanced.1.1.1⟩,[.frames 2,.arrayAllocation 16]++under 2 left.2++under 2 right.2++
    under 2 word.1.1.2++under 2 written.2++under 2 advanced.1.2),
    (46+BinaryRationalExpression.payloadWords left.1)+
      (46+BinaryRationalExpression.payloadWords right.1)+word.1.2+
      (56+BinaryRationalExpression.payloadWords word.1.1.1)+advanced.2+8),word.2)

def execute (instruction : Instruction) (registers : Registers) : (Registers × Trace) × ℕ :=
  (executeMeasured instruction registers).1

theorem executeMeasured_compat (instruction : Instruction) (registers : Registers) :
    (executeMeasured instruction registers).1 = execute instruction registers := rfl

theorem execute_erases (instruction : Instruction) (registers : Registers) :
    (execute instruction registers).1 = BinaryQuadraticResourcePairLifetime.executeWithTrace instruction registers := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,execute,executeMeasured,BinaryQuadraticMeasured.applyMeasured_compat,
    BinaryQuadraticResourcePairLifetime.executeWithTrace,
    BinaryQuadraticMeasured.apply_erases,BinaryHeapEnumerationMeasured.advance_erases]

theorem execute_data (instruction : Instruction) (registers : Registers) :
    (execute instruction registers).1.1 = (BinaryPRGWordControllerPairRegisters.executeWithWork instruction registers).1 := by
  rw [execute_erases,BinaryQuadraticResourcePairLifetime.executeWithTrace_erases,
    BinaryPRGWordControllerPairRegisters.executeWithWork_erasure]

theorem execute_work (instruction : Instruction) (registers : Registers) :
    (execute instruction registers).2 = (BinaryPRGWordControllerPairRegisters.executeWithWork instruction registers).2 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,execute,executeMeasured,BinaryQuadraticMeasured.applyMeasured_compat,
    BinaryPRGWordControllerPairRegisters.executeWithWork,
    BinaryQuadraticResourcePairLifetime.lookupWithTrace_erases,
    BinaryQuadraticMeasured.apply_work,BinaryQuadraticMeasured.apply_data,
    BinaryHeapEnumerationMeasured.advance_work,lookupCells_exact,updateCells_exact]

theorem executeMeasured_division_work_bound (instruction : Instruction) (registers : Registers) :
    (executeMeasured instruction registers).2 ≤ 4*(execute instruction registers).2 := by
  have h := BinaryQuadraticMeasured.applyMeasured_division_work_bound instruction.op
    (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.left).1
    (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.right).1
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,BinaryQuadraticMeasured.apply] at h
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,execute,executeMeasured]
  omega

def runMeasured : List Instruction → Registers → ((Registers × Trace) × ℕ) × ℕ
  | [],registers => (((registers,[.frames 1,.arrayAllocation 8]),1),0)
  | instruction::rest,registers =>
      let next := executeMeasured instruction registers
      let later := runMeasured rest next.1.1.1
      (((later.1.1.1,[.frames 2,.arrayAllocation 8]++under 2 next.1.1.2++under 1 later.1.1.2),
        next.1.2+later.1.2+2),next.2+later.2)

def run (program : List Instruction) (registers : Registers) : (Registers × Trace) × ℕ :=
  (runMeasured program registers).1

theorem runMeasured_compat (program : List Instruction) (registers : Registers) :
    (runMeasured program registers).1 = run program registers := rfl

theorem run_erases (program : List Instruction) (registers : Registers) :
    (run program registers).1 = BinaryQuadraticResourcePairLifetime.runWithTrace program registers := by
  induction program generalizing registers with
  | nil => rfl
  | cons instruction rest ih =>
      change (runMeasured (instruction::rest) registers).1.1 = _
      rw [runMeasured]
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,executeMeasured_compat,runMeasured_compat,
        BinaryQuadraticResourcePairLifetime.runWithTrace,execute_erases,ih]

theorem run_data (program : List Instruction) (registers : Registers) :
    (run program registers).1.1 = (BinaryPRGWordControllerPairRegisters.runWithWork program registers).1 := by
  rw [run_erases,BinaryQuadraticResourcePairLifetime.runWithTrace_erases,
    BinaryPRGWordControllerPairRegisters.runWithWork_erasure]

theorem run_work (program : List Instruction) (registers : Registers) :
    (run program registers).2 = (BinaryPRGWordControllerPairRegisters.runWithWork program registers).2 := by
  induction program generalizing registers with
  | nil => rfl
  | cons instruction rest ih =>
      change (runMeasured (instruction::rest) registers).1.2 = _
      rw [runMeasured]
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,executeMeasured_compat,runMeasured_compat,
        BinaryPRGWordControllerPairRegisters.runWithWork,execute_work,execute_data,ih]

theorem runMeasured_division_work_bound (program : List Instruction) (registers : Registers) :
    (runMeasured program registers).2 ≤ 4*(run program registers).2 := by
  induction program generalizing registers with
  | nil => simp [run,runMeasured]
  | cons instruction rest ih =>
      have hNext := executeMeasured_division_work_bound instruction registers
      have hLater := ih (executeMeasured instruction registers).1.1.1
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,execute] at hNext
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,run] at hLater
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,run,runMeasured]
      omega

def initial (source : BinaryRationalPairProgram.Source) : (Registers × Trace) × ℕ :=
  let initialized := BinaryQuadraticResourcePairLifetime.initialWithTrace source
  (initialized,218+copiedPayload initialized.1.tree)

theorem initial_erases (source : BinaryRationalPairProgram.Source) :
    (initial source).1 = BinaryQuadraticResourcePairLifetime.initialWithTrace source := rfl

theorem initial_work (source : BinaryRationalPairProgram.Source) :
    (initial source).2 = (BinaryPRGWordControllerPairRegisters.initialWithWork source).2 := by
  have hVisits := buildVisits_exact BinaryRationalOpcode.zero [false,false,false,false] (initialWords source)
  norm_num only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reducePow] at hVisits
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,initial,BinaryPRGWordControllerPairRegisters.initialWithWork,
    BinaryQuadraticResourcePairLifetime.initialWithTrace_erases]
  omega

def pairMeasured (source : BinaryRationalPairProgram.Source) : ((Registers × Trace) × ℕ) × ℕ :=
  let init := initial source
  let completed := runMeasured code init.1.1
  (((completed.1.1.1,[.frames 2,.arrayAllocation 8]++under 2 init.1.2++under 2 completed.1.1.2),
    init.2+completed.1.2),completed.2)

def pair (source : BinaryRationalPairProgram.Source) : (Registers × Trace) × ℕ := (pairMeasured source).1

theorem pairMeasured_compat (source : BinaryRationalPairProgram.Source) : (pairMeasured source).1 = pair source := rfl

theorem pair_erases (source : BinaryRationalPairProgram.Source) :
    (pair source).1 = BinaryQuadraticResourcePairLifetime.preparedPairWithTrace source := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,pair,pairMeasured,runMeasured_compat,
    BinaryQuadraticResourcePairLifetime.preparedPairWithTrace,initial_erases,run_erases]

theorem pair_work (source : BinaryRationalPairProgram.Source) :
    (pair source).2 = (BinaryPRGWordControllerPairRegisters.preparedPairWithWork source).2 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,pair,pairMeasured,runMeasured_compat,
    BinaryPRGWordControllerPairRegisters.preparedPairWithWork,initial_work,run_work,
    initial_erases,BinaryQuadraticResourcePairLifetime.initialWithTrace_erases]
  rfl

theorem pairMeasured_division_work_bound (source : BinaryRationalPairProgram.Source) :
    (pairMeasured source).2 ≤ 4*(pair source).2 := by
  have h := runMeasured_division_work_bound code (initial source).1.1
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,run] at h
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,pair,pairMeasured]
  omega

def outputsMeasured (source : BinaryRationalPairProgram.Source) :
    ((BinaryPRGWordControllerPairOutputs.Outputs × Trace) × ℕ) × ℕ :=
  let registers := pairMeasured source
  let lower := BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.1.1.1.tree a7
  let upper := BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.1.1.1.tree a8
  let probability := BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.1.1.1.tree a11
  (((⟨lower.1,upper.1,probability.1⟩,[.frames 2,.arrayAllocation 16]++under 2 registers.1.1.2++
      under 2 lower.2++under 2 upper.2++under 2 probability.2),
    registers.1.2+(46+BinaryRationalExpression.payloadWords lower.1)+
      (46+BinaryRationalExpression.payloadWords upper.1)+(46+BinaryRationalExpression.payloadWords probability.1)+6),registers.2)

def outputs (source : BinaryRationalPairProgram.Source) : (BinaryPRGWordControllerPairOutputs.Outputs × Trace) × ℕ :=
  (outputsMeasured source).1

theorem outputsMeasured_compat (source : BinaryRationalPairProgram.Source) :
    (outputsMeasured source).1 = outputs source := rfl

theorem outputs_erases (source : BinaryRationalPairProgram.Source) :
    (outputs source).1 = BinaryQuadraticResourcePairLifetime.outputsWithTrace source := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,outputs,outputsMeasured,pairMeasured_compat,
    BinaryQuadraticResourcePairLifetime.outputsWithTrace,pair_erases]

theorem outputs_data (source : BinaryRationalPairProgram.Source) :
    (outputs source).1.1 = (BinaryPRGWordControllerPairOutputs.prepareWithWork source).1 := by
  rw [outputs_erases,BinaryQuadraticResourcePairLifetime.outputsWithTrace_erases,
    BinaryPRGWordControllerPairOutputs.prepareWithWork_erasure]

theorem outputs_work (source : BinaryRationalPairProgram.Source) :
    (outputs source).2 = (BinaryPRGWordControllerPairOutputs.prepareWithWork source).2 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,outputs,outputsMeasured,pairMeasured_compat,
    BinaryPRGWordControllerPairOutputs.prepareWithWork,pair_work,pair_erases,
    BinaryQuadraticResourcePairLifetime.preparedPairWithTrace_erases,
    BinaryPRGWordControllerPairRegisters.preparedPairWithWork_erasure,
    BinaryQuadraticResourcePairLifetime.lookupWithTrace_erases,lookupCells_exact]

theorem outputsMeasured_division_work_bound (source : BinaryRationalPairProgram.Source) :
    (outputsMeasured source).2 ≤ 4*(outputs source).2 := by
  have h := pairMeasured_division_work_bound source
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,pair] at h
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,outputs,outputsMeasured]
  omega

end Blotto.BinaryHeapPairRegistersMeasured
