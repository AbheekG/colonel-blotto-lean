import Blotto.BinarySeedPreparationSpace
import Blotto.BinaryRationalOpcodeAllocation
import Blotto.BinaryRationalExpressionStorage

/-! Selected-path data-only AST evaluation joins actual opcode/comparison
allocation workspaces to evaluator activations. The old expression word is
exact; counters and traces are ghost annotations. Every primitive reservation
and source record stays retained until return. Environment/literal cells are
borrowed. The model is the existing arithmetic allocation backend, not a space
certificate for a different GCD implementation or a physical allocator/GC.
-/
set_option autoImplicit false
namespace Blotto.BinaryExpressionLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryRationalExpression

def combine (op : RealArithmeticOp) (a b : SignedWord×Trace) : SignedWord×Trace :=
  let out := BinaryRationalOpcodeAllocation.applyWithAllocation op a.1 b.1
  (out.1,[.frames 1,.arrayAllocation 8,.listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage op a.1 b.1)] ++
    under 1 a.2 ++ under 1 b.2)

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
      let comparison := BinaryRationalOpcodeAllocation.lessEqualWithAllocation x.1 y.1
      let selected := if comparison.1 then evaluate env yes else evaluate env no
      (selected.1,[.frames 1,.arrayAllocation 8,
        .listAllocation (BinaryRationalOpcodeAllocation.lessEqualStorage x.1 y.1)] ++
        under 1 x.2 ++ under 1 y.2 ++ under 1 selected.2)

theorem evaluate_erases {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k) :
    (evaluate env e).1=(e.run env).1 := by
  induction e with
  | input _ | literal _ => rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      simp only [evaluate,combine,BinaryRationalExpression.run,ha,hb,BinaryRationalOpcodeAllocation.applyWithAllocation_state]
  | ifLe a b yes no ha hb hy hn =>
      simp only [evaluate,BinaryRationalExpression.run,ha,hb,BinaryRationalOpcodeAllocation.lessEqualWithAllocation_state]
      split <;> simp only [hy,hn]

def stepBound (W : ℕ) : ℕ := 2000000*(W+2)^4+2500*(W+1)^3+8

theorem payload_width (word : SignedWord) (P : ℕ) (h : BinaryRationalExpression.payloadWords word ≤ P) : width word ≤ P := by
  unfold BinaryRationalExpression.payloadWords width at *
  omega

theorem combine_space (op : RealArithmeticOp) (a b : SignedWord×Trace) (P A B : ℕ)
    (ha : width a.1 ≤ P) (hb : width b.1 ≤ P)
    (hA : listCells a.2+arraySlots a.2 ≤ A) (hB : listCells b.2+arraySlots b.2 ≤ B) :
    listCells (combine op a b).2+arraySlots (combine op a b).2 ≤ A+B+stepBound P := by
  have hOp := (BinaryRationalOpcodeAllocation.opcodeStorage_bound op a.1 b.1).trans
    (Nat.mul_le_mul_left 2000000 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le ha hb) 2) 4))
  simp only [combine,listCells_append,arraySlots_append,listCells,arraySlots,listCells_under,arraySlots_under]
  unfold stepBound
  omega

set_option maxHeartbeats 1000000 in
theorem evaluate_space {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k) (P : ℕ)
    (h : e.ResultWordsBounded env P) :
    listCells (evaluate env e).2+arraySlots (evaluate env e).2 ≤ (e.run env).2*stepBound P := by
  induction e with
  | input _ | literal _ => simp [evaluate,BinaryRationalExpression.run,listCells,arraySlots,stepBound]
  | add a b ha hb =>
      have hA := ha h.1
      have hB := hb h.2.1
      have hAW := payload_width _ P (ResultWordsBounded.output a env P h.1)
      have hBW := payload_width _ P (ResultWordsBounded.output b env P h.2.1)
      have hAT : width (evaluate env a).1 ≤ P := by rw [evaluate_erases]; exact hAW
      have hBT : width (evaluate env b).1 ≤ P := by rw [evaluate_erases]; exact hBW
      have hCombined := combine_space .add (evaluate env a) (evaluate env b) P ((a.run env).2*stepBound P)
        ((b.run env).2*stepBound P) hAT hBT hA hB
      simp only [evaluate,BinaryRationalExpression.run]
      nlinarith only [hCombined]
  | sub a b ha hb =>
      have hA := ha h.1
      have hB := hb h.2.1
      have hAW := payload_width _ P (ResultWordsBounded.output a env P h.1)
      have hBW := payload_width _ P (ResultWordsBounded.output b env P h.2.1)
      have hAT : width (evaluate env a).1 ≤ P := by rw [evaluate_erases]; exact hAW
      have hBT : width (evaluate env b).1 ≤ P := by rw [evaluate_erases]; exact hBW
      have hCombined := combine_space .sub (evaluate env a) (evaluate env b) P ((a.run env).2*stepBound P)
        ((b.run env).2*stepBound P) hAT hBT hA hB
      simp only [evaluate,BinaryRationalExpression.run]
      nlinarith only [hCombined]
  | mul a b ha hb =>
      have hA := ha h.1
      have hB := hb h.2.1
      have hAW := payload_width _ P (ResultWordsBounded.output a env P h.1)
      have hBW := payload_width _ P (ResultWordsBounded.output b env P h.2.1)
      have hAT : width (evaluate env a).1 ≤ P := by rw [evaluate_erases]; exact hAW
      have hBT : width (evaluate env b).1 ≤ P := by rw [evaluate_erases]; exact hBW
      have hCombined := combine_space .mul (evaluate env a) (evaluate env b) P ((a.run env).2*stepBound P)
        ((b.run env).2*stepBound P) hAT hBT hA hB
      simp only [evaluate,BinaryRationalExpression.run]
      nlinarith only [hCombined]
  | div a b ha hb =>
      have hA := ha h.1
      have hB := hb h.2.1
      have hAW := payload_width _ P (ResultWordsBounded.output a env P h.1)
      have hBW := payload_width _ P (ResultWordsBounded.output b env P h.2.1)
      have hAT : width (evaluate env a).1 ≤ P := by rw [evaluate_erases]; exact hAW
      have hBT : width (evaluate env b).1 ≤ P := by rw [evaluate_erases]; exact hBW
      have hCombined := combine_space .div (evaluate env a) (evaluate env b) P ((a.run env).2*stepBound P)
        ((b.run env).2*stepBound P) hAT hBT hA hB
      simp only [evaluate,BinaryRationalExpression.run]
      nlinarith only [hCombined]
  | minimum a b ha hb =>
      have hA := ha h.1
      have hB := hb h.2.1
      have hAW := payload_width _ P (ResultWordsBounded.output a env P h.1)
      have hBW := payload_width _ P (ResultWordsBounded.output b env P h.2.1)
      have hAT : width (evaluate env a).1 ≤ P := by rw [evaluate_erases]; exact hAW
      have hBT : width (evaluate env b).1 ≤ P := by rw [evaluate_erases]; exact hBW
      have hCombined := combine_space .minimum (evaluate env a) (evaluate env b) P ((a.run env).2*stepBound P)
        ((b.run env).2*stepBound P) hAT hBT hA hB
      simp only [evaluate,BinaryRationalExpression.run]
      nlinarith only [hCombined]
  | maximum a b ha hb =>
      have hA := ha h.1
      have hB := hb h.2.1
      have hAW := payload_width _ P (ResultWordsBounded.output a env P h.1)
      have hBW := payload_width _ P (ResultWordsBounded.output b env P h.2.1)
      have hAT : width (evaluate env a).1 ≤ P := by rw [evaluate_erases]; exact hAW
      have hBT : width (evaluate env b).1 ≤ P := by rw [evaluate_erases]; exact hBW
      have hCombined := combine_space .maximum (evaluate env a) (evaluate env b) P ((a.run env).2*stepBound P)
        ((b.run env).2*stepBound P) hAT hBT hA hB
      simp only [evaluate,BinaryRationalExpression.run]
      nlinarith only [hCombined]
  | ifLe a b yes no ha hb hy hn =>
      have hA := ha h.1
      have hB := hb h.2.1
      have hYes := hy h.2.2.1
      have hNo := hn h.2.2.2
      have hAW := payload_width _ P (ResultWordsBounded.output a env P h.1)
      have hBW := payload_width _ P (ResultWordsBounded.output b env P h.2.1)
      have hCompare := (BinaryRationalOpcodeAllocation.lessEqualStorage_bound (a.run env).1 (b.run env).1).trans
        (Nat.mul_le_mul_left 2500 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le hAW hBW) 1) 3))
      have hLocal : BinaryRationalOpcodeAllocation.lessEqualStorage (a.run env).1 (b.run env).1+8 ≤ stepBound P := by
        unfold stepBound
        omega
      simp only [evaluate,listCells_append,arraySlots_append,listCells,arraySlots,listCells_under,arraySlots_under,
        evaluate_erases,BinaryRationalOpcodeAllocation.lessEqualWithAllocation_state,BinaryRationalExpression.run]
      split <;> nlinarith only [hA,hB,hYes,hNo,hLocal]

theorem evaluate_frames {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k) :
    framePeak (evaluate env e).2 ≤ e.depth+1 := by
  induction e with
  | input _ | literal _ => simp [evaluate,framePeak,BinaryRationalExpression.depth]
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      have hA := framePeak_under 1 (evaluate env a).2
      have hB := framePeak_under 1 (evaluate env b).2
      simp only [evaluate,combine,framePeak_append,framePeak,BinaryRationalExpression.depth]
      omega
  | ifLe a b yes no ha hb hy hn =>
      have hA := framePeak_under 1 (evaluate env a).2
      have hB := framePeak_under 1 (evaluate env b).2
      have hYes := framePeak_under 1 (evaluate env yes).2
      have hNo := framePeak_under 1 (evaluate env no).2
      simp only [evaluate,framePeak_append,framePeak,BinaryRationalExpression.depth]
      split <;> omega

theorem evaluate_height_contract {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k)
    (hEnv : ∀ j,CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) :
    (evaluate env e).1=(e.run env).1 ∧
    listCells (evaluate env e).2+arraySlots (evaluate env e).2 ≤ e.interpreted.operationBound*stepBound (8*s+7) ∧
    framePeak (evaluate env e).2 ≤ e.depth+1 := by
  have hWords := e.resultWords_of_heights env hEnv hLit s hHeight
  have hCount := e.run_count_le env (fun j => (hEnv j).1) (canonicalLiterals_valid e hLit)
  exact ⟨evaluate_erases env e,(evaluate_space env e (8*s+7) hWords).trans (Nat.mul_le_mul_right _ hCount),evaluate_frames env e⟩

theorem evaluate_all_prefix {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k)
    (hEnv : ∀ j,CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) (borrowedCells steps : ℕ) :
    retainedHeap borrowedCells (evaluate env e).2 steps ≤ borrowedCells+e.interpreted.operationBound*stepBound (8*s+7) := by
  have hb := (evaluate_height_contract env e hEnv hLit s hHeight).2.1
  have hl := listCells_take_le (evaluate env e).2 steps
  have ha := arraySlots_take_le (evaluate env e).2 steps
  unfold retainedHeap
  omega

end Blotto.BinaryExpressionLifetime
