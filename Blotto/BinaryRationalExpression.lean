import Blotto.BinaryRationalOpcode
import Blotto.RationalExpression

/-! A Boolean rational expression interpreter preserves the retained selected
conditional branches. Literals are stored words, not runtime Rat values. The
source compiler must encode its literals/inputs separately; this module proves
exact semantics and validity without changing the rational expression scope. -/

namespace Blotto
open BinaryRationalNormalization

inductive BinaryRationalExpression (k : ℕ) where
  | input (j : Fin k)
  | literal (word : SignedWord)
  | add (a b : BinaryRationalExpression k)
  | sub (a b : BinaryRationalExpression k)
  | mul (a b : BinaryRationalExpression k)
  | div (a b : BinaryRationalExpression k)
  | minimum (a b : BinaryRationalExpression k)
  | maximum (a b : BinaryRationalExpression k)
  | ifLe (a b yes no : BinaryRationalExpression k)

namespace BinaryRationalExpression

noncomputable def interpreted {k : ℕ} : BinaryRationalExpression k → RationalExpression k
  | .input j => .input j
  | .literal word => .literal (value word)
  | .add a b => .add a.interpreted b.interpreted
  | .sub a b => .sub a.interpreted b.interpreted
  | .mul a b => .mul a.interpreted b.interpreted
  | .div a b => .div a.interpreted b.interpreted
  | .minimum a b => .minimum a.interpreted b.interpreted
  | .maximum a b => .maximum a.interpreted b.interpreted
  | .ifLe a b yes no => .ifLe a.interpreted b.interpreted yes.interpreted no.interpreted

noncomputable def interpretedEnvironment {k : ℕ} (env : FixedArrayTable k SignedWord) : FixedArrayTable k ℚ :=
  FixedArrayTable.ofFn (fun j => value (env.read j))

def Valid {k : ℕ} : BinaryRationalExpression k → Prop
  | .input _ => True
  | .literal word => BinaryRationalOpcode.Valid word
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b => a.Valid ∧ b.Valid
  | .ifLe a b yes no => a.Valid ∧ b.Valid ∧ yes.Valid ∧ no.Valid

def run {k : ℕ} (env : FixedArrayTable k SignedWord) : BinaryRationalExpression k → SignedWord × ℕ
  | .input j => (env.read j, 1)
  | .literal word => (word, 1)
  | .add a b => let x := a.run env; let y := b.run env; (BinaryRationalOpcode.apply .add x.1 y.1, x.2 + y.2 + 1)
  | .sub a b => let x := a.run env; let y := b.run env; (BinaryRationalOpcode.apply .sub x.1 y.1, x.2 + y.2 + 1)
  | .mul a b => let x := a.run env; let y := b.run env; (BinaryRationalOpcode.apply .mul x.1 y.1, x.2 + y.2 + 1)
  | .div a b => let x := a.run env; let y := b.run env; (BinaryRationalOpcode.apply .div x.1 y.1, x.2 + y.2 + 2)
  | .minimum a b => let x := a.run env; let y := b.run env; (BinaryRationalOpcode.apply .minimum x.1 y.1, x.2 + y.2 + 1)
  | .maximum a b => let x := a.run env; let y := b.run env; (BinaryRationalOpcode.apply .maximum x.1 y.1, x.2 + y.2 + 1)
  | .ifLe a b yes no =>
      let x := a.run env
      let y := b.run env
      let z := if BinaryRationalArithmetic.lessEqual x.1 y.1 then yes.run env else no.run env
      (z.1, x.2 + y.2 + z.2 + 1)

theorem run_valid {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, BinaryRationalOpcode.Valid (env.read j)) (h : e.Valid) :
    BinaryRationalOpcode.Valid (e.run env).1 := by
  induction e with
  | input j => exact hEnv j
  | literal word => exact h
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
    exact BinaryRationalOpcode.apply_valid _ _ _ (ha h.1) (hb h.2)
  | ifLe a b yes no ha hb hy hn =>
    unfold run
    dsimp only
    split
    · exact hy h.2.2.1
    · exact hn h.2.2.2

theorem run_value {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, BinaryRationalOpcode.Valid (env.read j)) (h : e.Valid) :
    value (e.run env).1 = (e.interpreted.run (interpretedEnvironment env)).1 := by
  induction e with
  | input j => simp [run, interpreted, interpretedEnvironment, RationalExpression.run, FixedArrayTable.read_ofFn]
  | literal word => rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb | minimum a b ha hb | maximum a b ha hb =>
    have hA := a.run_valid env hEnv h.1
    have hB := b.run_valid env hEnv h.2
    simp only [run, interpreted, RationalExpression.run]
    rw [BinaryRationalOpcode.apply_value _ _ _ hA hB, ha h.1, hb h.2]
    rfl
  | div a b ha hb =>
    have hA := a.run_valid env hEnv h.1
    have hB := b.run_valid env hEnv h.2
    simp only [run, interpreted]
    rw [BinaryRationalOpcode.apply_value _ _ _ hA hB, ha h.1, hb h.2]
    exact (RationalExpression.safe_div_value _ _ _).symm
  | ifLe a b yes no ha hb hy hn =>
    have hA := a.run_valid env hEnv h.1
    have hB := b.run_valid env hEnv h.2.1
    have hCmp := BinaryRationalArithmetic.lessEqual_iff (a.run env).1 (b.run env).1 hA hB
    rw [ha h.1, hb h.2.1] at hCmp
    simp only [run, interpreted, RationalExpression.run]
    by_cases hLe : (a.interpreted.run (interpretedEnvironment env)).1 ≤ (b.interpreted.run (interpretedEnvironment env)).1
    · rw [ite_eq_left (hCmp.mpr hLe), ite_eq_left hLe]
      exact hy h.2.2.1
    · have hFalse : BinaryRationalArithmetic.lessEqual (a.run env).1 (b.run env).1 = false := by
        cases he : BinaryRationalArithmetic.lessEqual (a.run env).1 (b.run env).1
        · rfl
        · exact False.elim (hLe (hCmp.mp he))
      simp only [hFalse, Bool.false_eq_true, ite_false, hLe]
      exact hn h.2.2.2

theorem run_count {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, BinaryRationalOpcode.Valid (env.read j)) (h : e.Valid) :
    (e.run env).2 = (e.interpreted.run (interpretedEnvironment env)).2 := by
  induction e with
  | input j => rfl
  | literal word => rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
    simp only [run, interpreted, RationalExpression.run, ha h.1, hb h.2]
  | ifLe a b yes no ha hb hy hn =>
    have hA := a.run_valid env hEnv h.1
    have hB := b.run_valid env hEnv h.2.1
    have hCmp := BinaryRationalArithmetic.lessEqual_iff (a.run env).1 (b.run env).1 hA hB
    rw [a.run_value env hEnv h.1, b.run_value env hEnv h.2.1] at hCmp
    simp only [run, interpreted, RationalExpression.run, ha h.1, hb h.2.1]
    by_cases hLe : (a.interpreted.run (interpretedEnvironment env)).1 ≤ (b.interpreted.run (interpretedEnvironment env)).1
    · rw [ite_eq_left (hCmp.mpr hLe), ite_eq_left hLe, hy h.2.2.1]
    · have hFalse : BinaryRationalArithmetic.lessEqual (a.run env).1 (b.run env).1 = false := by
        cases he : BinaryRationalArithmetic.lessEqual (a.run env).1 (b.run env).1
        · rfl
        · exact False.elim (hLe (hCmp.mp he))
      simp only [hFalse, Bool.false_eq_true, ite_false, hLe, hn h.2.2.2]

theorem run_count_le {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, BinaryRationalOpcode.Valid (env.read j)) (h : e.Valid) :
    (e.run env).2 ≤ e.interpreted.operationBound := by
  rw [e.run_count env hEnv h]
  exact e.interpreted.run_operations_le _

end BinaryRationalExpression
end Blotto
