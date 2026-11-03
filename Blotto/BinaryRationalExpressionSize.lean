import Blotto.BinaryRationalExpression
import Blotto.BinaryRationalEncoding

/-! Canonical Boolean expression leaves and opcode outputs transfer actual
rational-value height bounds to stored word widths, including selected branches.
The source compiler's literal encoding/height certificate remains explicit. -/

namespace Blotto
open BinaryRationalNormalization BinaryRationalEncoding
namespace BinaryRationalExpression

def CanonicalLiterals {k : ℕ} : BinaryRationalExpression k → Prop
  | .input _ => True
  | .literal word => CanonicalWord word
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b => a.CanonicalLiterals ∧ b.CanonicalLiterals
  | .ifLe a b yes no => a.CanonicalLiterals ∧ b.CanonicalLiterals ∧ yes.CanonicalLiterals ∧ no.CanonicalLiterals

theorem canonicalLiterals_valid {k : ℕ} (e : BinaryRationalExpression k) (h : e.CanonicalLiterals) : e.Valid := by
  induction e with
  | input _ => trivial
  | literal word => exact h.1
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
    exact ⟨ha h.1,hb h.2⟩
  | ifLe a b yes no ha hb hy hn => exact ⟨ha h.1,hb h.2.1,hy h.2.2.1,hn h.2.2.2⟩

theorem run_canonical {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (h : e.CanonicalLiterals) : CanonicalWord (e.run env).1 := by
  induction e with
  | input j => exact hEnv j
  | literal word => exact h
  | add a b ha hb =>
    have hA := ha h.1
    have hB := hb h.2
    refine ⟨BinaryRationalOpcode.apply_valid .add _ _ hA.1 hB.1, ?_⟩
    have he := BinaryRationalOpcode.apply_width .add _ _ hA.1 hB.1
    rw [← BinaryRationalOpcode.apply_value .add _ _ hA.1 hB.1] at he
    exact he
  | sub a b ha hb =>
    have hA := ha h.1
    have hB := hb h.2
    refine ⟨BinaryRationalOpcode.apply_valid .sub _ _ hA.1 hB.1, ?_⟩
    have he := BinaryRationalOpcode.apply_width .sub _ _ hA.1 hB.1
    rw [← BinaryRationalOpcode.apply_value .sub _ _ hA.1 hB.1] at he
    exact he
  | mul a b ha hb =>
    have hA := ha h.1
    have hB := hb h.2
    refine ⟨BinaryRationalOpcode.apply_valid .mul _ _ hA.1 hB.1, ?_⟩
    have he := BinaryRationalOpcode.apply_width .mul _ _ hA.1 hB.1
    rw [← BinaryRationalOpcode.apply_value .mul _ _ hA.1 hB.1] at he
    exact he
  | div a b ha hb =>
    have hA := ha h.1
    have hB := hb h.2
    refine ⟨BinaryRationalOpcode.apply_valid .div _ _ hA.1 hB.1, ?_⟩
    have he := BinaryRationalOpcode.apply_width .div _ _ hA.1 hB.1
    rw [← BinaryRationalOpcode.apply_value .div _ _ hA.1 hB.1] at he
    exact he
  | minimum a b ha hb =>
    have hA := ha h.1
    have hB := hb h.2
    refine ⟨BinaryRationalOpcode.apply_valid .minimum _ _ hA.1 hB.1, ?_⟩
    have he := BinaryRationalOpcode.apply_width .minimum _ _ hA.1 hB.1
    rw [← BinaryRationalOpcode.apply_value .minimum _ _ hA.1 hB.1] at he
    exact he
  | maximum a b ha hb =>
    have hA := ha h.1
    have hB := hb h.2
    refine ⟨BinaryRationalOpcode.apply_valid .maximum _ _ hA.1 hB.1, ?_⟩
    have he := BinaryRationalOpcode.apply_width .maximum _ _ hA.1 hB.1
    rw [← BinaryRationalOpcode.apply_value .maximum _ _ hA.1 hB.1] at he
    exact he
  | ifLe a b yes no ha hb hy hn =>
    unfold run
    dsimp only
    split
    · exact hy h.2.2.1
    · exact hn h.2.2.2

theorem run_height_width {k : ℕ} (e : BinaryRationalExpression k) (env : FixedArrayTable k SignedWord)
    (hEnv : ∀ j, CanonicalWord (env.read j)) (h : e.CanonicalLiterals) (s : ℕ)
    (hHeight : RationalHeight (e.interpreted.run (interpretedEnvironment env)).1 s) :
    width (e.run env).1 ≤ 1 + 2 * s := by
  have hC := e.run_canonical env hEnv h
  have hV := e.run_value env (fun j => (hEnv j).1) (e.canonicalLiterals_valid h)
  have hWord := hC.2
  rw [hV] at hWord
  exact hWord.trans (rationalWordWidth_of_height hHeight)

end BinaryRationalExpression
end Blotto
