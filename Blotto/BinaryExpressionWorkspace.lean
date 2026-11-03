import Blotto.BinaryRationalExpressionStorage
import Blotto.BinaryRationalOpcodeAllocation

/-! Native selected-path expression evaluation composes structurally proved
Boolean opcode and signed-comparator buffers. Executed primitive workspaces are
conservatively retained until expression return; live result words/control
depth use the separate selected-path observer. Unselected branches contribute
only their stored literal data, not runtime primitive workspace. The model is
abstract Boolean/list-cell storage, not physical allocator/GC behavior. -/

namespace Blotto
open BinaryRationalNormalization BinaryRationalEncoding
namespace BinaryRationalExpression

def primitiveWorkspace {k : ℕ} (env : FixedArrayTable k SignedWord) : BinaryRationalExpression k → ℕ
  | .input _ | .literal _ => 0
  | .add a b => a.primitiveWorkspace env + b.primitiveWorkspace env +
      BinaryRationalOpcodeAllocation.opcodeStorage .add (a.run env).1 (b.run env).1
  | .sub a b => a.primitiveWorkspace env + b.primitiveWorkspace env +
      BinaryRationalOpcodeAllocation.opcodeStorage .sub (a.run env).1 (b.run env).1
  | .mul a b => a.primitiveWorkspace env + b.primitiveWorkspace env +
      BinaryRationalOpcodeAllocation.opcodeStorage .mul (a.run env).1 (b.run env).1
  | .div a b => a.primitiveWorkspace env + b.primitiveWorkspace env +
      BinaryRationalOpcodeAllocation.opcodeStorage .div (a.run env).1 (b.run env).1
  | .minimum a b => a.primitiveWorkspace env + b.primitiveWorkspace env +
      BinaryRationalOpcodeAllocation.opcodeStorage .minimum (a.run env).1 (b.run env).1
  | .maximum a b => a.primitiveWorkspace env + b.primitiveWorkspace env +
      BinaryRationalOpcodeAllocation.opcodeStorage .maximum (a.run env).1 (b.run env).1
  | .ifLe a b yes no => a.primitiveWorkspace env + b.primitiveWorkspace env +
      BinaryRationalOpcodeAllocation.lessEqualStorage (a.run env).1 (b.run env).1 +
      if BinaryRationalArithmetic.lessEqual (a.run env).1 (b.run env).1
      then yes.primitiveWorkspace env else no.primitiveWorkspace env

def runWithWorkspace {k : ℕ} (env : FixedArrayTable k SignedWord) :
    BinaryRationalExpression k → (SignedWord × ℕ) × ℕ
  | .input j => ((env.read j, 1), 0)
  | .literal word => ((word, 1), 0)
  | .add a b =>
      let x := a.runWithWorkspace env; let y := b.runWithWorkspace env
      let out := BinaryRationalOpcodeAllocation.applyWithAllocation .add x.1.1 y.1.1
      ((out.1, x.1.2 + y.1.2 + 1), x.2 + y.2 + BinaryRationalOpcodeAllocation.opcodeStorage .add x.1.1 y.1.1)
  | .sub a b =>
      let x := a.runWithWorkspace env; let y := b.runWithWorkspace env
      let out := BinaryRationalOpcodeAllocation.applyWithAllocation .sub x.1.1 y.1.1
      ((out.1, x.1.2 + y.1.2 + 1), x.2 + y.2 + BinaryRationalOpcodeAllocation.opcodeStorage .sub x.1.1 y.1.1)
  | .mul a b =>
      let x := a.runWithWorkspace env; let y := b.runWithWorkspace env
      let out := BinaryRationalOpcodeAllocation.applyWithAllocation .mul x.1.1 y.1.1
      ((out.1, x.1.2 + y.1.2 + 1), x.2 + y.2 + BinaryRationalOpcodeAllocation.opcodeStorage .mul x.1.1 y.1.1)
  | .div a b =>
      let x := a.runWithWorkspace env; let y := b.runWithWorkspace env
      let out := BinaryRationalOpcodeAllocation.applyWithAllocation .div x.1.1 y.1.1
      ((out.1, x.1.2 + y.1.2 + 2), x.2 + y.2 + BinaryRationalOpcodeAllocation.opcodeStorage .div x.1.1 y.1.1)
  | .minimum a b =>
      let x := a.runWithWorkspace env; let y := b.runWithWorkspace env
      let out := BinaryRationalOpcodeAllocation.applyWithAllocation .minimum x.1.1 y.1.1
      ((out.1, x.1.2 + y.1.2 + 1), x.2 + y.2 + BinaryRationalOpcodeAllocation.opcodeStorage .minimum x.1.1 y.1.1)
  | .maximum a b =>
      let x := a.runWithWorkspace env; let y := b.runWithWorkspace env
      let out := BinaryRationalOpcodeAllocation.applyWithAllocation .maximum x.1.1 y.1.1
      ((out.1, x.1.2 + y.1.2 + 1), x.2 + y.2 + BinaryRationalOpcodeAllocation.opcodeStorage .maximum x.1.1 y.1.1)
  | .ifLe a b yes no =>
      let x := a.runWithWorkspace env; let y := b.runWithWorkspace env
      let compared := BinaryRationalOpcodeAllocation.lessEqualWithAllocation x.1.1 y.1.1
      let z := if compared.1 then yes.runWithWorkspace env else no.runWithWorkspace env
      ((z.1.1, x.1.2 + y.1.2 + z.1.2 + 1),
        x.2 + y.2 + BinaryRationalOpcodeAllocation.lessEqualStorage x.1.1 y.1.1 + z.2)

theorem runWithWorkspace_refines {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord) :
    e.runWithWorkspace env = (e.run env, e.primitiveWorkspace env) := by
  induction e with
  | input _ | literal _ => rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      simp only [runWithWorkspace, run, primitiveWorkspace, ha, hb,
        BinaryRationalOpcodeAllocation.applyWithAllocation_state]
  | ifLe a b yes no ha hb hy hn =>
      simp only [runWithWorkspace, run, primitiveWorkspace, ha, hb,
        BinaryRationalOpcodeAllocation.lessEqualWithAllocation_state]
      split <;> simp only [hy, hn]

def workspacePrice (s : ℕ) : ℕ := 2000000 * (2 * s + 3) ^ 4

theorem opcodeWorkspace_height (op : RealArithmeticOp) (x y : SignedWord) (s : ℕ)
    (hX : width x ≤ 1 + 2 * s) (hY : width y ≤ 1 + 2 * s) :
    BinaryRationalOpcodeAllocation.opcodeStorage op x y ≤ workspacePrice s := by
  have h := BinaryRationalOpcodeAllocation.opcodeStorage_bound op x y
  have hw : BinaryRationalArithmetic.pairWidth x y + 2 ≤ 2 * s + 3 := by unfold BinaryRationalArithmetic.pairWidth; omega
  exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw 4))

theorem comparatorWorkspace_height (x y : SignedWord) (s : ℕ)
    (hX : width x ≤ 1 + 2 * s) (hY : width y ≤ 1 + 2 * s) :
    BinaryRationalOpcodeAllocation.lessEqualStorage x y ≤ workspacePrice s := by
  have h := BinaryRationalOpcodeAllocation.lessEqualStorage_bound x y
  have hw : BinaryRationalArithmetic.pairWidth x y + 1 ≤ 2 * s + 3 := by unfold BinaryRationalArithmetic.pairWidth; omega
  have hp : (2 * s + 3) ^ 3 ≤ (2 * s + 3) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have he := (Nat.pow_le_pow_left hw 3).trans hp
  unfold workspacePrice
  exact (h.trans (Nat.mul_le_mul_left _ he)).trans (Nat.mul_le_mul_right _ (by decide : 2500 ≤ 2000000))

theorem primitiveWorkspace_operations {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) :
    e.primitiveWorkspace env ≤ (e.run env).2 * workspacePrice s := by
  induction e with
  | input _ | literal _ => simp only [primitiveWorkspace, run]; positivity
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
      have hA := ha hLit.1 hHeight.2.2.1
      have hB := hb hLit.2 hHeight.2.2.2
      have hX := a.run_height_width env hEnv hLit.1 s hHeight.1
      have hY := b.run_height_width env hEnv hLit.2 s hHeight.2.1
      have hAdd := opcodeWorkspace_height .add _ _ s hX hY
      have hSub := opcodeWorkspace_height .sub _ _ s hX hY
      have hMul := opcodeWorkspace_height .mul _ _ s hX hY
      have hDiv := opcodeWorkspace_height .div _ _ s hX hY
      have hMin := opcodeWorkspace_height .minimum _ _ s hX hY
      have hMax := opcodeWorkspace_height .maximum _ _ s hX hY
      simp only [primitiveWorkspace, run]
      nlinarith
  | ifLe a b yes no ha hb hy hn =>
      have hA := ha hLit.1 hHeight.2.2.1
      have hB := hb hLit.2.1 hHeight.2.2.2.1
      have hYes := hy hLit.2.2.1 hHeight.2.2.2.2.1
      have hNo := hn hLit.2.2.2 hHeight.2.2.2.2.2
      have hCmp := comparatorWorkspace_height _ _ s
        (a.run_height_width env hEnv hLit.1 s hHeight.1)
        (b.run_height_width env hEnv hLit.2.1 s hHeight.2.1)
      simp only [primitiveWorkspace, run]
      split <;> nlinarith

theorem primitiveWorkspace_bound {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s) :
    e.primitiveWorkspace env ≤ e.interpreted.operationBound * workspacePrice s :=
  (e.primitiveWorkspace_operations env hEnv hLit s hHeight).trans
    (Nat.mul_le_mul_right _ (e.run_count_le env (fun j => (hEnv j).1) (e.canonicalLiterals_valid hLit)))

def syntaxNodes {k : ℕ} : BinaryRationalExpression k → ℕ
  | .input _ | .literal _ => 1
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b => 1 + a.syntaxNodes + b.syntaxNodes
  | .ifLe a b yes no => 1 + a.syntaxNodes + b.syntaxNodes + yes.syntaxNodes + no.syntaxNodes

-- Static AST node records and literal payload count both branches. Runtime
-- primitive scratch, result peak and control depth follow the selected branch.
-- Four cells per AST/control record conservatively charge its tag/references.
def evaluationStorageWithWorkspace {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord) : ℕ :=
  e.evaluationPayloadPeak env + 4 * ((e.runWithStorage env).2.2 + e.syntaxNodes + 1) + e.primitiveWorkspace env

theorem evaluationStorageWithWorkspace_bound {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s)
    (hEnvHeight : ∀ j, RationalHeight (value (env.read j)) s) :
    e.evaluationStorageWithWorkspace env ≤ k * (4 * s + 3) +
      (e.literalCount + 3 * (e.depth + 1)) * (8 * s + 7) +
      4 * (e.depth + e.syntaxNodes + 2) + e.interpreted.operationBound * workspacePrice s := by
  have hp := (e.evaluationStorage_contract env hEnv hLit s hHeight hEnvHeight).2.1
  have hc := e.controlDepth_bound env
  have hw := e.primitiveWorkspace_bound env hEnv hLit s hHeight
  unfold evaluationStorageWithWorkspace
  omega

theorem evaluationWorkspace_contract {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (hLit : e.CanonicalLiterals) (s : ℕ)
    (hHeight : e.interpreted.AllRunHeights (interpretedEnvironment env) s)
    (hEnvHeight : ∀ j, RationalHeight (value (env.read j)) s) :
    (e.runWithWorkspace env).1 = e.run env ∧
      (e.runWithWorkspace env).2 = e.primitiveWorkspace env ∧
      e.evaluationStorageWithWorkspace env ≤ k * (4 * s + 3) +
        (e.literalCount + 3 * (e.depth + 1)) * (8 * s + 7) +
        4 * (e.depth + e.syntaxNodes + 2) + e.interpreted.operationBound * workspacePrice s := by
  rw [e.runWithWorkspace_refines]
  exact ⟨rfl, rfl, e.evaluationStorageWithWorkspace_bound env hEnv hLit s hHeight hEnvHeight⟩

end BinaryRationalExpression
end Blotto
