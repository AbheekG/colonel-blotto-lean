import Blotto.BinaryRegisterTreePlan
import Blotto.BinaryRegisterMetadataPlan

/-! Actual planned register storage replaces the old recursive trace leaves.
Reached reversal/tree/wrapper visits are forwarded through every instruction
and the actual returned register state, then added to one final emission.
Actual payload/tree metadata scans supply exact old source charges, and cursor
carry builds its final-depth plan. Full old records and public bounds remain. -/
namespace Blotto.BinaryRegisterStoragePlan
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerPairRegisters
open BinaryTracePlanMeasured BinaryTraceDepth BinaryPRGHeapTraceUsage
open BinaryNumericalReadbackPlan (view offset data_refines trace_refines charge_refines)
open BinaryCachePrefixPlan (Bounded)
set_option autoImplicit false
set_option maxHeartbeats 5000000

abbrev Result (α : Type*) := BinaryPairRegisterPlan.Record α × ℕ

def Safe {α : Type*} (produced : Result α) : Prop :=
  Bounded produced.1.1.2 ∧ produced.2 ≤ payload produced.1.1.2

def executeAt (instruction : Instruction) (registers : Registers) (depth : ℕ) : Result Registers :=
  let left := BinaryRegisterTreePlan.lookupAt registers.tree instruction.left (depth+2)
  let right := BinaryRegisterTreePlan.lookupAt registers.tree instruction.right (depth+2)
  let word := BinaryNormalizationPlan.applyAt instruction.op left.1.1 right.1.1 (depth+2)
  let written := BinaryRegisterTreePlan.writeAt registers.tree registers.cursor word.1.1 (depth+2)
  let advanced := BinaryRegisterMetadataPlan.cursorAt registers.cursor (depth+2)
  (((⟨written.1.1,advanced.1.1.1⟩,.join (.block [.frames (depth+2),.arrayAllocation 16])
    (.join left.1.2 (.join right.1.2 (.join word.1.2 (.join written.1.2 advanced.1.2))))),
    (BinaryRegisterMetadataPlan.readCharge left.1.1+
      BinaryRegisterMetadataPlan.readCharge right.1.1+word.2.1+
      BinaryRegisterMetadataPlan.writeCharge word.1.1+advanced.2+8,word.2.2)),left.2+right.2+written.2)

theorem execute_refines (instruction : Instruction) (registers : Registers) (depth : ℕ) :
    view (executeAt instruction registers depth).1 = offset depth
      ((BinaryHeapPairRegistersMeasured.executeMeasured instruction registers).1.1,
        ((BinaryHeapPairRegistersMeasured.executeMeasured instruction registers).1.2,
          (BinaryHeapPairRegistersMeasured.executeMeasured instruction registers).2)) := by
  have hl := BinaryRegisterTreePlan.lookup_refines registers.tree instruction.left (depth+2)
  have hr := BinaryRegisterTreePlan.lookup_refines registers.tree instruction.right (depth+2)
  have h := BinaryNormalizationPlan.apply_refines instruction.op
    (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.left).1
    (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.right).1 (depth+2)
  have hw := BinaryRegisterTreePlan.write_refines registers.tree registers.cursor
    (BinaryQuadraticMeasured.applyMeasured instruction.op
      (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.left).1
      (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.right).1).1.1.1 (depth+2)
  have ha := BinaryRegisterMetadataPlan.cursor_refines registers.cursor (depth+2)
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,executeAt,BinaryHeapPairRegistersMeasured.executeMeasured,view,offset,denote,
    BinaryRegisterMetadataPlan.read_exact,BinaryRegisterMetadataPlan.write_exact,
    data_refines ha,trace_refines ha,charge_refines ha,
    hl.1,hl.2,hr.1,hr.2,data_refines h,trace_refines h,charge_refines h,hw.1,hw.2,
    under_append,under_compose,List.append_assoc]
  rfl

theorem execute_safe (instruction : Instruction) (registers : Registers) (depth : ℕ) : Safe (executeAt instruction registers depth) := by
  have hl := BinaryRegisterTreePlan.lookup_safe registers.tree instruction.left (depth+2)
  have hr := BinaryRegisterTreePlan.lookup_safe registers.tree instruction.right (depth+2)
  have h := BinaryNormalizationPlan.apply_budget instruction.op
    (BinaryRegisterTreePlan.lookupAt registers.tree instruction.left (depth+2)).1.1
    (BinaryRegisterTreePlan.lookupAt registers.tree instruction.right (depth+2)).1.1 (depth+2)
  have hw := BinaryRegisterTreePlan.write_safe registers.tree registers.cursor
    (BinaryNormalizationPlan.applyAt instruction.op
      (BinaryRegisterTreePlan.lookupAt registers.tree instruction.left (depth+2)).1.1
      (BinaryRegisterTreePlan.lookupAt registers.tree instruction.right (depth+2)).1.1 (depth+2)).1.1 (depth+2)
  have ha := BinaryRegisterMetadataPlan.cursor_bound registers.cursor (depth+2)
  simp only [executeAt,Safe,Bounded,BinaryRegisterTreePlan.Safe,nodes,payload,List.length_cons,List.length_nil] at hl hr h hw ha ⊢
  constructor <;> omega

def runAt : List Instruction → Registers → ℕ → Result Registers
  | [],registers,depth => (((registers,.block [.frames (depth+1),.arrayAllocation 8]),(1,0)),0)
  | instruction::rest,registers,depth =>
      let next := executeAt instruction registers (depth+2)
      let later := runAt rest next.1.1.1 (depth+1)
      (((later.1.1.1,.join (.block [.frames (depth+2),.arrayAllocation 8]) (.join next.1.1.2 later.1.1.2)),
        (next.1.2.1+later.1.2.1+2,next.1.2.2+later.1.2.2)),next.2+later.2)

theorem run_refines (program : List Instruction) (registers : Registers) (depth : ℕ) :
    view (runAt program registers depth).1 = offset depth
      ((BinaryHeapPairRegistersMeasured.runMeasured program registers).1.1,
        ((BinaryHeapPairRegistersMeasured.runMeasured program registers).1.2,
          (BinaryHeapPairRegistersMeasured.runMeasured program registers).2)) := by
  induction program generalizing registers depth with
  | nil => rfl
  | cons instruction rest ih =>
      have hn := execute_refines instruction registers (depth+2)
      have hl := ih (BinaryHeapPairRegistersMeasured.executeMeasured instruction registers).1.1.1 (depth+1)
      simp only [runAt,BinaryHeapPairRegistersMeasured.runMeasured,view,offset,denote,
        data_refines hn,trace_refines hn,charge_refines hn,data_refines hl,trace_refines hl,charge_refines hl,
        under_append,under_compose,List.append_assoc]
      rfl

theorem run_safe (program : List Instruction) (registers : Registers) (depth : ℕ) : Safe (runAt program registers depth) := by
  induction program generalizing registers depth with
  | nil => simp [runAt,Safe,Bounded,nodes,payload]
  | cons instruction rest ih =>
      have hn := execute_safe instruction registers (depth+2)
      have hl := ih (executeAt instruction registers (depth+2)).1.1.1 (depth+1)
      simp only [runAt,Safe,Bounded,nodes,payload,List.length_cons,List.length_nil] at hn hl ⊢
      constructor <;> omega

def pairAt (source : BinaryRationalPairProgram.Source) (depth : ℕ) : Result Registers :=
  let init := BinaryRegisterTreePlan.initialAt source (depth+2)
  let completed := runAt code init.1.1 (depth+2)
  (((completed.1.1.1,.join (.block [.frames (depth+2),.arrayAllocation 8]) (.join init.1.2 completed.1.1.2)),
    (BinaryRegisterMetadataPlan.initialCharge init.1.1.tree+completed.1.2.1,completed.1.2.2)),init.2+completed.2)

theorem pair_refines (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    view (pairAt source depth).1 = offset depth
      ((BinaryHeapPairRegistersMeasured.pairMeasured source).1.1,
        ((BinaryHeapPairRegistersMeasured.pairMeasured source).1.2,
          (BinaryHeapPairRegistersMeasured.pairMeasured source).2)) := by
  have hi := BinaryRegisterTreePlan.initial_refines source (depth+2)
  have h := run_refines code (BinaryHeapPairRegistersMeasured.initial source).1.1 (depth+2)
  simp only [pairAt,BinaryHeapPairRegistersMeasured.pairMeasured,view,offset,denote,
    hi.1,hi.2,BinaryRegisterMetadataPlan.initial_exact,data_refines h,trace_refines h,charge_refines h,under_append,under_compose,List.append_assoc]
  rfl

theorem pair_safe (source : BinaryRationalPairProgram.Source) (depth : ℕ) : Safe (pairAt source depth) := by
  have hi := BinaryRegisterTreePlan.initial_safe source (depth+2)
  have h := run_safe code (BinaryRegisterTreePlan.initialAt source (depth+2)).1.1 (depth+2)
  simp only [pairAt,Safe,Bounded,BinaryRegisterTreePlan.Safe,nodes,payload,List.length_cons,List.length_nil] at hi h ⊢
  constructor <;> omega

def outputsAt (source : BinaryRationalPairProgram.Source) (depth : ℕ) : Result BinaryPRGWordControllerPairOutputs.Outputs :=
  let registers := pairAt source (depth+2)
  let lower := BinaryRegisterTreePlan.lookupAt registers.1.1.1.tree a7 (depth+2)
  let upper := BinaryRegisterTreePlan.lookupAt registers.1.1.1.tree a8 (depth+2)
  let probability := BinaryRegisterTreePlan.lookupAt registers.1.1.1.tree a11 (depth+2)
  (((⟨lower.1.1,upper.1.1,probability.1.1⟩,.join (.block [.frames (depth+2),.arrayAllocation 16])
      (.join registers.1.1.2 (.join lower.1.2 (.join upper.1.2 probability.1.2)))),
    (registers.1.2.1+BinaryRegisterMetadataPlan.readCharge lower.1.1+
      BinaryRegisterMetadataPlan.readCharge upper.1.1+BinaryRegisterMetadataPlan.readCharge probability.1.1+6,
      registers.1.2.2)),registers.2+lower.2+upper.2+probability.2)

theorem outputs_refines (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    view (outputsAt source depth).1 = offset depth
      ((BinaryHeapPairRegistersMeasured.outputsMeasured source).1.1,
        ((BinaryHeapPairRegistersMeasured.outputsMeasured source).1.2,
          (BinaryHeapPairRegistersMeasured.outputsMeasured source).2)) := by
  have h := pair_refines source (depth+2)
  have hl := BinaryRegisterTreePlan.lookup_refines (BinaryHeapPairRegistersMeasured.pairMeasured source).1.1.1.tree a7 (depth+2)
  have hu := BinaryRegisterTreePlan.lookup_refines (BinaryHeapPairRegistersMeasured.pairMeasured source).1.1.1.tree a8 (depth+2)
  have hp := BinaryRegisterTreePlan.lookup_refines (BinaryHeapPairRegistersMeasured.pairMeasured source).1.1.1.tree a11 (depth+2)
  simp only [outputsAt,BinaryHeapPairRegistersMeasured.outputsMeasured,view,offset,denote,
    BinaryRegisterMetadataPlan.read_exact,
    data_refines h,trace_refines h,charge_refines h,hl.1,hl.2,hu.1,hu.2,hp.1,hp.2,
    under_append,under_compose,List.append_assoc]
  rfl

theorem outputs_safe (source : BinaryRationalPairProgram.Source) (depth : ℕ) : Safe (outputsAt source depth) := by
  have h := pair_safe source (depth+2)
  have hl := BinaryRegisterTreePlan.lookup_safe (pairAt source (depth+2)).1.1.1.tree a7 (depth+2)
  have hu := BinaryRegisterTreePlan.lookup_safe (pairAt source (depth+2)).1.1.1.tree a8 (depth+2)
  have hp := BinaryRegisterTreePlan.lookup_safe (pairAt source (depth+2)).1.1.1.tree a11 (depth+2)
  simp only [outputsAt,Safe,Bounded,BinaryRegisterTreePlan.Safe,nodes,payload,List.length_cons,List.length_nil] at h hl hu hp ⊢
  constructor <;> omega

@[irreducible] def outputsWithEmission (source : BinaryRationalPairProgram.Source) :=
  let produced := outputsAt source 0
  let emitted := BinaryNormalizationPlan.finishMeasured produced.1
  (emitted.1,emitted.2+produced.2)

theorem outputs_compat (source : BinaryRationalPairProgram.Source) :
    (outputsWithEmission source).1 = BinaryHeapPairRegistersMeasured.outputsMeasured source := by
  unfold outputsWithEmission
  exact BinaryNormalizationPlan.finishMeasured_compat
    (record := (outputsAt source 0).1)
    (old := BinaryHeapPairRegistersMeasured.outputsMeasured source) (outputs_refines source 0)

theorem outputs_price (source : BinaryRationalPairProgram.Source) :
    (outputsWithEmission source).2 ≤ 25*(outputsWithEmission source).1.1.1.2.length+5 := by
  let produced := outputsAt source 0
  have hs := outputs_safe source 0
  have hShift := shiftCount_bound produced.1.1.2
  change Safe produced at hs
  simp only [Safe,Bounded] at hs
  simp only [outputsWithEmission,BinaryNormalizationPlan.finishMeasured,BinaryNumericalReadbackPlan.finish,
    emitFull_erases,emit_work,emitFull_shifts,emit_length,List.length_nil,Nat.add_zero]
  change 4*payload produced.1.1.2+2*nodes produced.1.1.2+shiftCount produced.1.1.2+produced.2 ≤
    25*payload produced.1.1.2+5
  omega

end Blotto.BinaryRegisterStoragePlan
