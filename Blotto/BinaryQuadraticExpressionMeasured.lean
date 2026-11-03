import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryQuadraticMeasured
import Blotto.BinaryQuadraticExpressionLifetime

/-! The selected expression source consumes measured quadratic results and
reached comparisons once, returning the preceding word/trace and source work.
Only the chosen conditional branch runs. Environment/literal payloads are
borrowed; native addressing and observer/reference/allocator costs are separate. -/

namespace Blotto.BinaryQuadraticExpressionMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryRationalExpression
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 3000000

def compare (first second : SignedWord) : (Bool × Trace) × ℕ :=
  let result := BinaryRationalComparisonMeasured.compare first second
  ((result.data,[.frames (result.allocated+8),.arrayAllocation 8,.listAllocation result.storage]),
    payloadWords first+payloadWords second+result.work+4)

theorem compare_erases (first second : SignedWord) :
    (compare first second).1 = BinaryQuadraticExpressionLifetime.compareWithTrace first second := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,compare,BinaryQuadraticExpressionLifetime.compareWithTrace,
    BinaryRationalComparisonMeasured.compare_data,BinaryRationalComparisonMeasured.compare_allocated,
    BinaryRationalComparisonMeasured.compare_storage,BinaryRationalOpcodeAllocation.lessEqualWithAllocation_state]

theorem compare_data (first second : SignedWord) :
    (compare first second).1.1 = BinaryRationalArithmetic.lessEqual first second := by
  rw [compare_erases,BinaryQuadraticExpressionLifetime.compareWithTrace_erases]

theorem compare_work (first second : SignedWord) :
    (compare first second).2 = comparePrice first second := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,compare,comparePrice,BinaryRationalComparisonMeasured.compare_work]

set_option cleanup.letToHave false in
def combineWithExtras (op : RealArithmeticOp) (a b : ((SignedWord × Trace) × ℕ) × ℕ) : ((SignedWord × Trace) × ℕ) × ℕ :=
  let produced := BinaryNormalizedCoordinate.opcode op a.1.1.1 b.1.1.1
  let out := produced.1
  (((out.1.1,[.frames 2,.arrayAllocation 8]++under 1 a.1.1.2++under 1 b.1.1.2++under 2 out.1.2),
    a.1.2+b.1.2+payloadWords a.1.1.1+payloadWords b.1.1.1+out.2+4),a.2+b.2+produced.2)

def combine (op : RealArithmeticOp) (a b : (SignedWord × Trace) × ℕ) : (SignedWord × Trace) × ℕ :=
  (combineWithExtras op (a,0) (b,0)).1

theorem combineWithExtras_record (op : RealArithmeticOp) (a b : ((SignedWord × Trace) × ℕ) × ℕ) :
    (combineWithExtras op a b).1 = combine op a.1 b.1 := rfl

theorem combine_record (op : RealArithmeticOp) (a b : (SignedWord × Trace) × ℕ) :
    combine op a b =
  let out := BinaryPlannedQuadratic.apply op a.1.1 b.1.1
  ((out.1.1,[.frames 2,.arrayAllocation 8]++under 1 a.1.2++under 1 b.1.2++under 2 out.1.2),
    a.2+b.2+payloadWords a.1.1+payloadWords b.1.1+out.2+4)
 := by
  simp only [combine,combineWithExtras,BinaryNormalizedCoordinate.opcode_record]

theorem combine_erases (op : RealArithmeticOp) (a b : (SignedWord × Trace) × ℕ) :
    (combine op a b).1 = BinaryQuadraticExpressionLifetime.combine op a.1 b.1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,combine_record,BinaryQuadraticExpressionLifetime.combine,BinaryQuadraticMeasured.apply_erases]

set_option cleanup.letToHave false in
def evaluateWithExtras {k : ℕ} (env : FixedArrayTable k SignedWord) : BinaryRationalExpression k → ((SignedWord × Trace) × ℕ) × ℕ
  | .input j => (((env.read j,[.frames 1,.arrayAllocation 8]),payloadWords (env.read j)+1),0)
  | .literal word => (((word,[.frames 1,.arrayAllocation 8]),payloadWords word+1),0)
  | .add a b => combineWithExtras .add (evaluateWithExtras env a) (evaluateWithExtras env b)
  | .sub a b => combineWithExtras .sub (evaluateWithExtras env a) (evaluateWithExtras env b)
  | .mul a b => combineWithExtras .mul (evaluateWithExtras env a) (evaluateWithExtras env b)
  | .div a b => combineWithExtras .div (evaluateWithExtras env a) (evaluateWithExtras env b)
  | .minimum a b => combineWithExtras .minimum (evaluateWithExtras env a) (evaluateWithExtras env b)
  | .maximum a b => combineWithExtras .maximum (evaluateWithExtras env a) (evaluateWithExtras env b)
  | .ifLe a b yes no =>
      let x := evaluateWithExtras env a
      let y := evaluateWithExtras env b
      let compared := compare x.1.1.1 y.1.1.1
      let chosen := if compared.1.1 then evaluateWithExtras env yes else evaluateWithExtras env no
      (((chosen.1.1.1,[.frames 2,.arrayAllocation 8]++under 1 x.1.1.2++under 1 y.1.1.2++
        under 2 compared.1.2++under 1 chosen.1.1.2),x.1.2+y.1.2+compared.2+chosen.1.2),x.2+y.2+chosen.2)

def evaluate {k : ℕ} (env : FixedArrayTable k SignedWord) : BinaryRationalExpression k → (SignedWord × Trace) × ℕ :=
  fun e => (evaluateWithExtras env e).1

theorem evaluateWithExtras_compat {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k) :
    (evaluateWithExtras env e).1 = evaluate env e := rfl

theorem evaluate_record {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k) :
    evaluate env e = match e with
  | .input j => ((env.read j,[.frames 1,.arrayAllocation 8]),payloadWords (env.read j)+1)
  | .literal word => ((word,[.frames 1,.arrayAllocation 8]),payloadWords word+1)
  | .add a b => combine .add (evaluate env a) (evaluate env b)
  | .sub a b => combine .sub (evaluate env a) (evaluate env b)
  | .mul a b => combine .mul (evaluate env a) (evaluate env b)
  | .div a b => combine .div (evaluate env a) (evaluate env b)
  | .minimum a b => combine .minimum (evaluate env a) (evaluate env b)
  | .maximum a b => combine .maximum (evaluate env a) (evaluate env b)
  | .ifLe a b yes no =>
      let x := evaluate env a
      let y := evaluate env b
      let compared := compare x.1.1 y.1.1
      let chosen := if compared.1.1 then evaluate env yes else evaluate env no
      ((chosen.1.1,[.frames 2,.arrayAllocation 8]++under 1 x.1.2++under 1 y.1.2++
        under 2 compared.1.2++under 1 chosen.1.2),x.2+y.2+compared.2+chosen.2)
 := by
  cases e <;> dsimp only [evaluate,evaluateWithExtras]
  all_goals first | rfl | (split <;> rfl)

theorem evaluate_erases {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k) :
    (evaluate env e).1 = BinaryQuadraticExpressionLifetime.evaluate env e := by
  induction e with
  | input _ | literal _ => rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      rw [evaluate_record]
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,BinaryQuadraticExpressionLifetime.evaluate,combine_erases,ha,hb]
  | ifLe a b yes no ha hb hy hn =>
      rw [evaluate_record]
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,BinaryQuadraticExpressionLifetime.evaluate,ha,hb,compare_erases]
      split <;> rename_i h <;> simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,h,Bool.false_eq_true,ite_true,ite_false,hy,hn]

theorem evaluate_data {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k) :
    (evaluate env e).1.1 = (BinaryQuadraticExpression.run env e).1.1 := by
  rw [evaluate_erases,BinaryQuadraticExpressionLifetime.evaluate_erases,← BinaryQuadraticData.expression_erasure]

theorem evaluate_work {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k) :
    (evaluate env e).2 = (BinaryQuadraticExpression.run env e).2 := by
  induction e with
  | input _ | literal _ => rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      rw [evaluate_record]
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,combine_record,BinaryQuadraticExpression.run,BinaryQuadraticExpression.combine,
        evaluate_data,BinaryQuadraticMeasured.apply_work,ha,hb]
  | ifLe a b yes no ha hb hy hn =>
      rw [evaluate_record]
      simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,BinaryQuadraticExpression.run,evaluate_data,compare_data,compare_work,ha,hb]
      split <;> rename_i h <;> simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,h,Bool.false_eq_true,ite_true,ite_false,hy,hn]

theorem evaluate_work_bound {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k)
    (hEnv : ∀ j,CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) :
    (evaluate env e).2 ≤ e.interpreted.operationBound*BinaryQuadraticExpression.uniformPrice s := by
  rw [evaluate_work]
  exact BinaryQuadraticExpression.run_work_bound e env hEnv hLit s hHeight

theorem evaluate_all_prefix {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k)
    (hEnv : ∀ j,CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) (borrowed steps : ℕ) :
    retainedHeap borrowed (evaluate env e).1.2 steps ≤
      borrowed+e.interpreted.operationBound*BinaryQuadraticExpressionLifetime.stepBound (8*s+7) := by
  rw [evaluate_erases]
  exact BinaryQuadraticExpressionLifetime.evaluate_all_prefix env e hEnv hLit s hHeight borrowed steps

end Blotto.BinaryQuadraticExpressionMeasured
