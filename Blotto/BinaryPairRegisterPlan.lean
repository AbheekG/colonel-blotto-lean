import Blotto.BinaryHeapPairRegistersMeasured
import Blotto.BinaryNormalizationPlan

/-! Actual register instructions and their recursive program collect final-depth
plans. Each next instruction consumes the returned register tree/cursor once.
One output-boundary emission preserves complete old values/trace/source/division
records and returns reached work for the existing packed counter. Register
lookup/write/build/metadata and native/physical-space leaves retain their scope. -/
namespace Blotto.BinaryPairRegisterPlan
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerPairRegisters
open BinaryTracePlanMeasured BinaryTraceDepth BinaryPRGHeapTraceUsage
open BinaryNumericalReadbackPlan (view offset data_refines trace_refines charge_refines)
open BinaryCachePrefixPlan (Bounded)
set_option autoImplicit false
set_option maxHeartbeats 5000000

abbrev Record (α : Type*) := (α × Plan) × (ℕ × ℕ)

def executeAt (instruction : Instruction) (registers : Registers) (depth : ℕ) : Record Registers :=
  let left := BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.left
  let right := BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.right
  let word := BinaryNormalizationPlan.applyAt instruction.op left.1 right.1 (depth+2)
  let written := BinaryQuadraticResourcePairLifetime.writeWithTrace registers.tree registers.cursor word.1.1
  let advanced := BinaryHeapEnumerationMeasured.advance registers.cursor
  ((⟨written.1,advanced.1.1.1⟩,.join (.block [.frames (depth+2),.arrayAllocation 16])
    (.join (.shifted (depth+2) left.2) (.join (.shifted (depth+2) right.2)
      (.join word.1.2 (.join (.shifted (depth+2) written.2) (.shifted (depth+2) advanced.1.2)))))),
    ((46+BinaryRationalExpression.payloadWords left.1)+
      (46+BinaryRationalExpression.payloadWords right.1)+word.2.1+
      (56+BinaryRationalExpression.payloadWords word.1.1)+advanced.2+8,word.2.2))

theorem execute_refines (instruction : Instruction) (registers : Registers) (depth : ℕ) :
    view (executeAt instruction registers depth) = offset depth
      ((BinaryHeapPairRegistersMeasured.executeMeasured instruction registers).1.1,
        ((BinaryHeapPairRegistersMeasured.executeMeasured instruction registers).1.2,
          (BinaryHeapPairRegistersMeasured.executeMeasured instruction registers).2)) := by
  have h := BinaryNormalizationPlan.apply_refines instruction.op
    (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.left).1
    (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.right).1 (depth+2)
  simp only [BinaryPlannedQuadratic.applyMeasured_previous,executeAt,BinaryHeapPairRegistersMeasured.executeMeasured,view,offset,denote,
    data_refines h,trace_refines h,charge_refines h,under_append,under_compose,List.append_assoc]
  rfl

theorem execute_bounded (instruction : Instruction) (registers : Registers) (depth : ℕ) :
    Bounded (executeAt instruction registers depth).1.2 := by
  have h := BinaryNormalizationPlan.apply_budget instruction.op
    (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.left).1
    (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.right).1 (depth+2)
  have hl : 1 ≤ (BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.tree instruction.left).2.length := by
    simp [BinaryQuadraticResourcePairLifetime.lookupWithTrace]
  simp only [executeAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  omega

def runAt : List Instruction → Registers → ℕ → Record Registers
  | [],registers,depth => ((registers,.block [.frames (depth+1),.arrayAllocation 8]),(1,0))
  | instruction::rest,registers,depth =>
      let next := executeAt instruction registers (depth+2)
      let later := runAt rest next.1.1 (depth+1)
      ((later.1.1,.join (.block [.frames (depth+2),.arrayAllocation 8]) (.join next.1.2 later.1.2)),
        (next.2.1+later.2.1+2,next.2.2+later.2.2))

theorem run_refines (program : List Instruction) (registers : Registers) (depth : ℕ) :
    view (runAt program registers depth) = offset depth
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

theorem run_bounded (program : List Instruction) (registers : Registers) (depth : ℕ) :
    Bounded (runAt program registers depth).1.2 := by
  induction program generalizing registers depth with
  | nil => simp [runAt,Bounded,nodes,payload]
  | cons instruction rest ih =>
      have hn := execute_bounded instruction registers (depth+2)
      have hl := ih (executeAt instruction registers (depth+2)).1.1 (depth+1)
      simp only [runAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at hn hl ⊢
      omega

def pairAt (source : BinaryRationalPairProgram.Source) (depth : ℕ) : Record Registers :=
  let init := BinaryHeapPairRegistersMeasured.initial source
  let completed := runAt code init.1.1 (depth+2)
  ((completed.1.1,.join (.block [.frames (depth+2),.arrayAllocation 8])
    (.join (.shifted (depth+2) init.1.2) completed.1.2)),(init.2+completed.2.1,completed.2.2))

theorem pair_refines (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    view (pairAt source depth) = offset depth
      ((BinaryHeapPairRegistersMeasured.pairMeasured source).1.1,
        ((BinaryHeapPairRegistersMeasured.pairMeasured source).1.2,
          (BinaryHeapPairRegistersMeasured.pairMeasured source).2)) := by
  have h := run_refines code (BinaryHeapPairRegistersMeasured.initial source).1.1 (depth+2)
  simp only [pairAt,BinaryHeapPairRegistersMeasured.pairMeasured,view,offset,denote,
    data_refines h,trace_refines h,charge_refines h,under_append,under_compose,List.append_assoc]
  rfl

theorem pair_bounded (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    Bounded (pairAt source depth).1.2 := by
  have h := run_bounded code (BinaryHeapPairRegistersMeasured.initial source).1.1 (depth+2)
  simp only [pairAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  omega

def outputsAt (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    Record BinaryPRGWordControllerPairOutputs.Outputs :=
  let registers := pairAt source (depth+2)
  let lower := BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.1.1.tree a7
  let upper := BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.1.1.tree a8
  let probability := BinaryQuadraticResourcePairLifetime.lookupWithTrace registers.1.1.tree a11
  ((⟨lower.1,upper.1,probability.1⟩,.join (.block [.frames (depth+2),.arrayAllocation 16])
      (.join registers.1.2 (.join (.shifted (depth+2) lower.2)
        (.join (.shifted (depth+2) upper.2) (.shifted (depth+2) probability.2))))),
    (registers.2.1+(46+BinaryRationalExpression.payloadWords lower.1)+
      (46+BinaryRationalExpression.payloadWords upper.1)+(46+BinaryRationalExpression.payloadWords probability.1)+6,
      registers.2.2))

theorem outputs_refines (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    view (outputsAt source depth) = offset depth
      ((BinaryHeapPairRegistersMeasured.outputsMeasured source).1.1,
        ((BinaryHeapPairRegistersMeasured.outputsMeasured source).1.2,
          (BinaryHeapPairRegistersMeasured.outputsMeasured source).2)) := by
  have h := pair_refines source (depth+2)
  simp only [outputsAt,BinaryHeapPairRegistersMeasured.outputsMeasured,view,offset,denote,
    data_refines h,trace_refines h,charge_refines h,under_append,under_compose,List.append_assoc]
  rfl

theorem outputs_bounded (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    Bounded (outputsAt source depth).1.2 := by
  have h := pair_bounded source (depth+2)
  simp only [outputsAt,Bounded,nodes,payload,List.length_cons,List.length_nil] at h ⊢
  omega

@[irreducible] def outputsWithEmission (source : BinaryRationalPairProgram.Source) :=
  BinaryNormalizationPlan.finishMeasured (outputsAt source 0)

theorem outputs_compat (source : BinaryRationalPairProgram.Source) :
    (outputsWithEmission source).1 = BinaryHeapPairRegistersMeasured.outputsMeasured source := by
  unfold outputsWithEmission
  exact BinaryNormalizationPlan.finishMeasured_compat (outputs_refines source 0)

theorem outputs_price (source : BinaryRationalPairProgram.Source) :
    (outputsWithEmission source).2 ≤ 25*(outputsWithEmission source).1.1.1.2.length+5 := by
  unfold outputsWithEmission
  exact BinaryNormalizationPlan.finishMeasured_price (outputsAt source 0) (outputs_bounded source 0)

end Blotto.BinaryPairRegisterPlan
