import Blotto.GeneralPaperCodeStrictOrder

/-! The selected physical shift is smaller than every distinct decoded
closed-threshold gap. Actual physical bids therefore have the same strict
order as valid integer codes, including zero and closed one.
-/
namespace Blotto.GeneralPaperCodePhysicalOrder
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperCodeDecodeSound
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem physical_lower (choice : Choice) (delta : ℚ) (hDelta : 0≤delta) :
    choice.threshold.value≤choice.physical delta := by
  unfold Choice.physical
  cases choice.opened <;> simp [hDelta]

theorem physical_upper (choice : Choice) (delta : ℚ) (hDelta : 0≤delta) :
    choice.physical delta≤choice.threshold.value+delta := by
  unfold Choice.physical
  cases choice.opened <;> simp [hDelta]

theorem shift_lt_threshold_gap (a : Alphabet) (m qbar : ℕ) (hm : 0<m) (hQ : 0<qbar) :
    GeneralPaperTagBudgetTransfer.shift m qbar a.C<1/((a.C:ℚ)*(a.C:ℚ)) := by
  have hC := a.scalePositive
  have hp : a.C^2≤a.C^(m+2) := pow_le_pow_right₀ (by omega) (by omega)
  have hMQ : 1≤m*qbar := Nat.succ_le_of_lt (Nat.mul_pos hm hQ)
  have hb : a.C^2≤m*qbar*a.C^(m+2) :=
    hp.trans (by simpa only [one_mul] using Nat.mul_le_mul_right (a.C^(m+2)) hMQ)
  have hPositive : 0<m*qbar*a.C^(m+2) := by positivity
  have hDen : a.C*a.C<GeneralPaperTagBudgetTransfer.shiftDenominator m qbar a.C := by
    unfold GeneralPaperTagBudgetTransfer.shiftDenominator
    nlinarith only [hb,hPositive]
  have hDenPositive : (0:ℚ)<GeneralPaperTagBudgetTransfer.shiftDenominator m qbar a.C := by
    unfold GeneralPaperTagBudgetTransfer.shiftDenominator
    positivity
  have hSquare : (0:ℚ)<(a.C:ℚ)*(a.C:ℚ) := by positivity
  unfold GeneralPaperTagBudgetTransfer.shift
  apply (div_lt_div_iff₀ hDenPositive hSquare).mpr
  simpa only [one_mul] using (show (a.C:ℚ)*(a.C:ℚ)<(GeneralPaperTagBudgetTransfer.shiftDenominator m qbar a.C:ℚ) by exact_mod_cast hDen)

theorem physical_strict (a : Alphabet) (responseX responseY : Bool) (c d : ℕ) (x y : Choice)
    (hX : (decode a responseX c).choice=some x) (hY : (decode a responseY d).choice=some y)
    (hCode : c<d) (delta : ℚ) (hDelta : 0<delta) (hSmall : delta<1/((a.C:ℚ)*(a.C:ℚ))) :
    x.physical delta<y.physical delta := by
  have hTag := GeneralPaperCodeStrictOrder.decode_strict a responseX responseY c d x y hX hY hCode
  rcases (GeneralPaperCodeStrictOrder.tag_lt_iff x y).mp hTag with hValue|⟨hValue,hClosed,hOpen⟩
  · have hGap := Farey.bounded_separation a.C (decode_sound a responseX c x hX).2 (decode_sound a responseY d y hY).2 hValue
    have hUpper := physical_upper x delta hDelta.le
    have hLower := physical_lower y delta hDelta.le
    linarith only [hSmall,hGap,hUpper,hLower]
  · unfold Choice.physical
    rw [hClosed,hOpen]
    simp only [Bool.false_eq_true,ite_false,ite_true,add_zero]
    linarith only [hValue,hDelta]

theorem selected_physical_strict (a : Alphabet) (responseX responseY : Bool) (c d : ℕ) (x y : Choice)
    (hX : (decode a responseX c).choice=some x) (hY : (decode a responseY d).choice=some y)
    (hCode : c<d) (m qbar : ℕ) (hm : 0<m) (hQ : 0<qbar) :
    x.physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C)<y.physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C) :=
  physical_strict a responseX responseY c d x y hX hY hCode _
    (GeneralPaperTagBudgetTransfer.shift_positive m qbar a.C hm hQ a.scalePositive)
    (shift_lt_threshold_gap a m qbar hm hQ)

end Blotto.GeneralPaperCodePhysicalOrder
