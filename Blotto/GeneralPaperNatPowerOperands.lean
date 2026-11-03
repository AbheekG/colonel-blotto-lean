import Blotto.GeneralPaperIntegerWordPrice
import Blotto.GeneralPaperNatPower

/-! Literal repeated-squaring operands, including the unreduced square.
The final power bounds every recursively reached power when the base is
positive. The explicit word envelope is computed from the original inputs;
its logarithms belong to the proof and are not evaluated by the program.
-/
namespace Blotto.GeneralPaperNatPowerOperands
set_option autoImplicit false

theorem half_power (base exponent : ℕ) (hb : 0<base) :
    (GeneralPaperNatPower.run base (exponent/2)).power≤base^exponent ∧
    (GeneralPaperNatPower.run base (exponent/2)).power*
      (GeneralPaperNatPower.run base (exponent/2)).power≤base^exponent := by
  rw [(GeneralPaperNatPower.data base (exponent/2)).1]
  constructor
  · exact Nat.pow_le_pow_right hb (by omega)
  · rw [←pow_add]
    exact Nat.pow_le_pow_right hb (by omega)

def magnitude (base exponent : ℕ) : ℕ := 2+base+exponent+base^exponent

def width (base exponent : ℕ) : ℕ :=
  8+binaryWordWidth base+binaryWordWidth exponent+exponent*binaryWordWidth base

theorem power_width (base exponent : ℕ) :
    binaryWordWidth (base^exponent)≤1+exponent*binaryWordWidth base := by
  induction exponent with
  | zero => simp only [pow_zero,Nat.zero_mul,Nat.add_zero]; decide
  | succ n ih =>
    have hm := binaryWordWidth_mul (base^n) base
    rw [pow_succ]
    calc
      binaryWordWidth (base^n*base) ≤ binaryWordWidth (base^n)+binaryWordWidth base := hm
      _ ≤ 1+(n+1)*binaryWordWidth base := by nlinarith only [ih]

theorem magnitude_width (base exponent : ℕ) :
    1+binaryWordWidth (magnitude base exponent)≤width base exponent := by
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add 2 base
  have hb := GeneralPaperRayOperandWidthEnvelope.word_add (2+base) exponent
  have hc := GeneralPaperRayOperandWidthEnvelope.word_add (2+base+exponent) (base^exponent)
  have hp := power_width base exponent
  have ht : binaryWordWidth 2=2 := by decide
  unfold magnitude width
  omega

end Blotto.GeneralPaperNatPowerOperands
