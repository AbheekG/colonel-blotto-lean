import Blotto.BinaryQuadraticLifetime
import Blotto.BinaryExpressionLifetime

/-! Selected expression lifetime for the actual quadratic data-only backend.
Concrete raw/Stein/division/trim opcode reservations replace the Euclidean
normalization trace. Exact all-input data erasure and valid old expression
bytes hold. Reached words derive heap/activation bounds; source heights supply
those words without an execution hypothesis. Environment/literals are borrowed,
and all newly reserved child regions stay retained until return. -/
set_option autoImplicit false
namespace Blotto.BinaryQuadraticExpressionLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryRationalExpression

def compareWithTrace (first second : SignedWord) : Bool×Trace :=
  let result := BinaryRationalOpcodeAllocation.lessEqualWithAllocation first second
  (result.1,[.frames (result.2+8),.arrayAllocation 8,
    .listAllocation (BinaryRationalOpcodeAllocation.lessEqualStorage first second)])

@[simp] theorem compareWithTrace_erases (first second : SignedWord) :
    (compareWithTrace first second).1=BinaryRationalArithmetic.lessEqual first second :=
  BinaryRationalOpcodeAllocation.lessEqualWithAllocation_state first second

theorem compareWithTrace_bounds (first second : SignedWord) (P : ℕ)
    (hA : width first≤P) (hB : width second≤P) :
    listCells (compareWithTrace first second).2+arraySlots (compareWithTrace first second).2≤2500*(P+1)^3+8 ∧
    framePeak (compareWithTrace first second).2≤150*(P+1)^2+8 := by
  have hw : BinaryRationalArithmetic.pairWidth first second≤P := max_le hA hB
  have hSpace := (BinaryRationalOpcodeAllocation.lessEqualStorage_bound first second).trans
    (Nat.mul_le_mul_left 2500 (Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) 3))
  have hFrames := (BinaryRationalOpcodeAllocation.lessEqualWithAllocation_bound first second).trans
    (Nat.mul_le_mul_left 150 (Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) 2))
  simp only [compareWithTrace,listCells,arraySlots,framePeak]
  exact ⟨by omega,by omega⟩

def combine (op : RealArithmeticOp) (a b : SignedWord×Trace) : SignedWord×Trace :=
  let out := BinaryQuadraticLifetime.applyWithTrace op a.1 b.1
  (out.1,[.frames 2,.arrayAllocation 8] ++ under 1 a.2 ++ under 1 b.2 ++ under 2 out.2)

def evaluate {k : ℕ} (env : FixedArrayTable k SignedWord) : BinaryRationalExpression k → SignedWord×Trace
  | .input j => (env.read j,[.frames 1,.arrayAllocation 8])
  | .literal word => (word,[.frames 1,.arrayAllocation 8])
  | .add a b => combine .add (evaluate env a) (evaluate env b)
  | .sub a b => combine .sub (evaluate env a) (evaluate env b)
  | .mul a b => combine .mul (evaluate env a) (evaluate env b)
  | .div a b => combine .div (evaluate env a) (evaluate env b)
  | .minimum a b => combine .minimum (evaluate env a) (evaluate env b)
  | .maximum a b => combine .maximum (evaluate env a) (evaluate env b)
  | .ifLe a b yes no =>
      let x := evaluate env a
      let y := evaluate env b
      let compared := compareWithTrace x.1 y.1
      let chosen := if compared.1 then evaluate env yes else evaluate env no
      (chosen.1,[.frames 2,.arrayAllocation 8] ++ under 1 x.2 ++ under 1 y.2 ++ under 2 compared.2 ++ under 1 chosen.2)

@[simp] theorem evaluate_erases {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k) :
    (evaluate env e).1=BinaryQuadraticData.expression env e := by
  induction e with
  | input _ | literal _ => rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      simp only [evaluate,combine,BinaryQuadraticLifetime.applyWithTrace_erases,ha,hb,BinaryQuadraticData.expression]
  | ifLe a b yes no ha hb hy hn =>
      simp only [evaluate,compareWithTrace_erases,ha,hb,BinaryQuadraticData.expression]
      split <;> simp only [hy,hn]

theorem evaluate_state {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k)
    (hEnv : ∀ j,BinaryRationalOpcode.Valid (env.read j)) (h : e.Valid) :
    (evaluate env e).1=(e.run env).1 := by
  rw [evaluate_erases]
  exact BinaryQuadraticData.expression_state e env hEnv h

def stepBound (P : ℕ) : ℕ := BinaryQuadraticLifetime.opcodeBound P+2500*(P+1)^3+16
def frameBound (P : ℕ) : ℕ := BinaryQuadraticLifetime.opcodeFrames P+150*(P+1)^2+32

theorem combine_bounds (op : RealArithmeticOp) (a b : SignedWord×Trace) (P A B da db : ℕ)
    (ha : width a.1≤P) (hb : width b.1≤P)
    (hA : listCells a.2+arraySlots a.2≤A) (hB : listCells b.2+arraySlots b.2≤B)
    (hDA : framePeak a.2≤da+frameBound P+1) (hDB : framePeak b.2≤db+frameBound P+1) :
    listCells (combine op a b).2+arraySlots (combine op a b).2≤A+B+stepBound P ∧
    framePeak (combine op a b).2≤max da db+frameBound P+2 := by
  have hOp := BinaryQuadraticLifetime.applyWithTrace_bounds op a.1 b.1 P ha hb
  have hAF := framePeak_under 1 a.2
  have hBF := framePeak_under 1 b.2
  have hOF := framePeak_under 2 (BinaryQuadraticLifetime.applyWithTrace op a.1 b.1).2
  simp only [combine,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  unfold stepBound frameBound at *
  exact ⟨by omega,by omega⟩

set_option maxHeartbeats 2000000 in
theorem evaluate_bounds {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k)
    (hEnv : ∀ j,CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (P : ℕ)
    (hWords : e.ResultWordsBounded env P) :
    listCells (evaluate env e).2+arraySlots (evaluate env e).2≤(e.run env).2*stepBound P ∧
    framePeak (evaluate env e).2≤e.depth+frameBound P+1 := by
  induction e with
  | input _ | literal _ =>
      simp [evaluate,BinaryRationalExpression.run,listCells,arraySlots,framePeak,stepBound,frameBound,BinaryRationalExpression.depth]
  | add a b ha hb =>
      have hA := ha hLit.1 hWords.1
      have hB := hb hLit.2 hWords.2.1
      have hAW := BinaryExpressionLifetime.payload_width _ P (ResultWordsBounded.output a env P hWords.1)
      have hBW := BinaryExpressionLifetime.payload_width _ P (ResultWordsBounded.output b env P hWords.2.1)
      have hAT : width (evaluate env a).1≤P := by
        rw [evaluate_state env a (fun j => (hEnv j).1) (a.canonicalLiterals_valid hLit.1)]; exact hAW
      have hBT : width (evaluate env b).1≤P := by
        rw [evaluate_state env b (fun j => (hEnv j).1) (b.canonicalLiterals_valid hLit.2)]; exact hBW
      have hCombined := combine_bounds .add (evaluate env a) (evaluate env b) P
        ((a.run env).2*stepBound P) ((b.run env).2*stepBound P) a.depth b.depth hAT hBT hA.1 hB.1 hA.2 hB.2
      simp only [evaluate,BinaryRationalExpression.run,BinaryRationalExpression.depth]
      exact ⟨by nlinarith only [hCombined.1],by omega⟩
  | sub a b ha hb =>
      have hA := ha hLit.1 hWords.1
      have hB := hb hLit.2 hWords.2.1
      have hAW := BinaryExpressionLifetime.payload_width _ P (ResultWordsBounded.output a env P hWords.1)
      have hBW := BinaryExpressionLifetime.payload_width _ P (ResultWordsBounded.output b env P hWords.2.1)
      have hAT : width (evaluate env a).1≤P := by
        rw [evaluate_state env a (fun j => (hEnv j).1) (a.canonicalLiterals_valid hLit.1)]; exact hAW
      have hBT : width (evaluate env b).1≤P := by
        rw [evaluate_state env b (fun j => (hEnv j).1) (b.canonicalLiterals_valid hLit.2)]; exact hBW
      have hCombined := combine_bounds .sub (evaluate env a) (evaluate env b) P
        ((a.run env).2*stepBound P) ((b.run env).2*stepBound P) a.depth b.depth hAT hBT hA.1 hB.1 hA.2 hB.2
      simp only [evaluate,BinaryRationalExpression.run,BinaryRationalExpression.depth]
      exact ⟨by nlinarith only [hCombined.1],by omega⟩
  | mul a b ha hb =>
      have hA := ha hLit.1 hWords.1
      have hB := hb hLit.2 hWords.2.1
      have hAW := BinaryExpressionLifetime.payload_width _ P (ResultWordsBounded.output a env P hWords.1)
      have hBW := BinaryExpressionLifetime.payload_width _ P (ResultWordsBounded.output b env P hWords.2.1)
      have hAT : width (evaluate env a).1≤P := by
        rw [evaluate_state env a (fun j => (hEnv j).1) (a.canonicalLiterals_valid hLit.1)]; exact hAW
      have hBT : width (evaluate env b).1≤P := by
        rw [evaluate_state env b (fun j => (hEnv j).1) (b.canonicalLiterals_valid hLit.2)]; exact hBW
      have hCombined := combine_bounds .mul (evaluate env a) (evaluate env b) P
        ((a.run env).2*stepBound P) ((b.run env).2*stepBound P) a.depth b.depth hAT hBT hA.1 hB.1 hA.2 hB.2
      simp only [evaluate,BinaryRationalExpression.run,BinaryRationalExpression.depth]
      exact ⟨by nlinarith only [hCombined.1],by omega⟩
  | div a b ha hb =>
      have hA := ha hLit.1 hWords.1
      have hB := hb hLit.2 hWords.2.1
      have hAW := BinaryExpressionLifetime.payload_width _ P (ResultWordsBounded.output a env P hWords.1)
      have hBW := BinaryExpressionLifetime.payload_width _ P (ResultWordsBounded.output b env P hWords.2.1)
      have hAT : width (evaluate env a).1≤P := by
        rw [evaluate_state env a (fun j => (hEnv j).1) (a.canonicalLiterals_valid hLit.1)]; exact hAW
      have hBT : width (evaluate env b).1≤P := by
        rw [evaluate_state env b (fun j => (hEnv j).1) (b.canonicalLiterals_valid hLit.2)]; exact hBW
      have hCombined := combine_bounds .div (evaluate env a) (evaluate env b) P
        ((a.run env).2*stepBound P) ((b.run env).2*stepBound P) a.depth b.depth hAT hBT hA.1 hB.1 hA.2 hB.2
      simp only [evaluate,BinaryRationalExpression.run,BinaryRationalExpression.depth]
      exact ⟨by nlinarith only [hCombined.1],by omega⟩
  | minimum a b ha hb =>
      have hA := ha hLit.1 hWords.1
      have hB := hb hLit.2 hWords.2.1
      have hAW := BinaryExpressionLifetime.payload_width _ P (ResultWordsBounded.output a env P hWords.1)
      have hBW := BinaryExpressionLifetime.payload_width _ P (ResultWordsBounded.output b env P hWords.2.1)
      have hAT : width (evaluate env a).1≤P := by
        rw [evaluate_state env a (fun j => (hEnv j).1) (a.canonicalLiterals_valid hLit.1)]; exact hAW
      have hBT : width (evaluate env b).1≤P := by
        rw [evaluate_state env b (fun j => (hEnv j).1) (b.canonicalLiterals_valid hLit.2)]; exact hBW
      have hCombined := combine_bounds .minimum (evaluate env a) (evaluate env b) P
        ((a.run env).2*stepBound P) ((b.run env).2*stepBound P) a.depth b.depth hAT hBT hA.1 hB.1 hA.2 hB.2
      simp only [evaluate,BinaryRationalExpression.run,BinaryRationalExpression.depth]
      exact ⟨by nlinarith only [hCombined.1],by omega⟩
  | maximum a b ha hb =>
      have hA := ha hLit.1 hWords.1
      have hB := hb hLit.2 hWords.2.1
      have hAW := BinaryExpressionLifetime.payload_width _ P (ResultWordsBounded.output a env P hWords.1)
      have hBW := BinaryExpressionLifetime.payload_width _ P (ResultWordsBounded.output b env P hWords.2.1)
      have hAT : width (evaluate env a).1≤P := by
        rw [evaluate_state env a (fun j => (hEnv j).1) (a.canonicalLiterals_valid hLit.1)]; exact hAW
      have hBT : width (evaluate env b).1≤P := by
        rw [evaluate_state env b (fun j => (hEnv j).1) (b.canonicalLiterals_valid hLit.2)]; exact hBW
      have hCombined := combine_bounds .maximum (evaluate env a) (evaluate env b) P
        ((a.run env).2*stepBound P) ((b.run env).2*stepBound P) a.depth b.depth hAT hBT hA.1 hB.1 hA.2 hB.2
      simp only [evaluate,BinaryRationalExpression.run,BinaryRationalExpression.depth]
      exact ⟨by nlinarith only [hCombined.1],by omega⟩
  | ifLe a b yes no ha hb hy hn =>
      have hA := ha hLit.1 hWords.1
      have hB := hb hLit.2.1 hWords.2.1
      have hYes := hy hLit.2.2.1 hWords.2.2.1
      have hNo := hn hLit.2.2.2 hWords.2.2.2
      have hAW := BinaryExpressionLifetime.payload_width _ P (ResultWordsBounded.output a env P hWords.1)
      have hBW := BinaryExpressionLifetime.payload_width _ P (ResultWordsBounded.output b env P hWords.2.1)
      have hAT : width (evaluate env a).1≤P := by
        rw [evaluate_state env a (fun j => (hEnv j).1) (a.canonicalLiterals_valid hLit.1)]; exact hAW
      have hBT : width (evaluate env b).1≤P := by
        rw [evaluate_state env b (fun j => (hEnv j).1) (b.canonicalLiterals_valid hLit.2.1)]; exact hBW
      have hCmp := compareWithTrace_bounds (evaluate env a).1 (evaluate env b).1 P hAT hBT
      have hAF := framePeak_under 1 (evaluate env a).2
      have hBF := framePeak_under 1 (evaluate env b).2
      have hCF := framePeak_under 2 (compareWithTrace (evaluate env a).1 (evaluate env b).1).2
      have hYF := framePeak_under 1 (evaluate env yes).2
      have hNF := framePeak_under 1 (evaluate env no).2
      have hLocal : listCells (compareWithTrace (evaluate env a).1 (evaluate env b).1).2+
          arraySlots (compareWithTrace (evaluate env a).1 (evaluate env b).1).2+8≤stepBound P := by
        unfold stepBound; omega
      have hLocalF : framePeak (under 2 (compareWithTrace (evaluate env a).1 (evaluate env b).1).2)≤frameBound P := by
        unfold frameBound; omega
      have hBaseFrames : 2≤frameBound P := by unfold frameBound; omega
      rw [evaluate_state env a (fun j => (hEnv j).1) (a.canonicalLiterals_valid hLit.1),
        evaluate_state env b (fun j => (hEnv j).1) (b.canonicalLiterals_valid hLit.2.1)] at hLocal hLocalF
      simp only [evaluate,listCells_append,arraySlots_append,listCells,arraySlots,listCells_under,arraySlots_under,
        framePeak_append,framePeak,BinaryRationalExpression.run,BinaryRationalExpression.depth,compareWithTrace_erases]
      rw [evaluate_state env a (fun j => (hEnv j).1) (a.canonicalLiterals_valid hLit.1),
        evaluate_state env b (fun j => (hEnv j).1) (b.canonicalLiterals_valid hLit.2.1)]
      split <;> exact ⟨by nlinarith only [hA.1,hB.1,hYes.1,hNo.1,hLocal],by omega⟩

theorem evaluate_height_contract {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k)
    (hEnv : ∀ j,CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) :
    (evaluate env e).1=(e.run env).1 ∧
    listCells (evaluate env e).2+arraySlots (evaluate env e).2≤e.interpreted.operationBound*stepBound (8*s+7) ∧
    framePeak (evaluate env e).2≤e.depth+frameBound (8*s+7)+1 := by
  have hWords := e.resultWords_of_heights env hEnv hLit s hHeight
  have hEval := evaluate_bounds env e hEnv hLit (8*s+7) hWords
  have hCount := e.run_count_le env (fun j => (hEnv j).1) (e.canonicalLiterals_valid hLit)
  exact ⟨evaluate_state env e (fun j => (hEnv j).1) (e.canonicalLiterals_valid hLit),
    hEval.1.trans (Nat.mul_le_mul_right _ hCount),hEval.2⟩

theorem evaluate_all_prefix {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k)
    (hEnv : ∀ j,CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) (borrowedCells steps : ℕ) :
    retainedHeap borrowedCells (evaluate env e).2 steps≤borrowedCells+e.interpreted.operationBound*stepBound (8*s+7) :=
  BinaryBooleanPrimitiveLifetime.prefix_heap _ _ _ _ (evaluate_height_contract env e hEnv hLit s hHeight).2.1

end Blotto.BinaryQuadraticExpressionLifetime
