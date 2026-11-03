import Blotto.GeneralPaperSourceParameterPrice

/-! Uniform word bounds for constructed dyadics and doubling ceilings.
Zero targets are covered too. These are analytical operand sizes, not
calls that inspect or encode an original real input.
-/
namespace Blotto.GeneralPaperParameterOperandBounds
set_option autoImplicit false

def ceilingProfile (primitive : ℕ → ℕ) (W target : ℕ) : ℕ :=
  64*(binaryWordWidth target+1)*(W+primitive (1+binaryWordWidth (2*(target+1))))

theorem ceiling_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W target : ℕ) :
    (GeneralPaperPowerCeilingBits.run primitive W target).2≤ceilingProfile primitive W target :=
  GeneralPaperPowerCeilingBits.work primitive hMono W target

theorem dyadic_word (e : ℕ) :
    binaryWordWidth (GeneralPaperScoreScaleParameters.powerRun e).power≤1+2*e := by
  rw [(GeneralPaperScoreScaleParameters.power_data e).1]
  simpa only [show binaryWordWidth 2=2 by decide,Nat.mul_comm] using GeneralPaperNatPowerOperands.power_width 2 e

theorem max_word (a b : ℕ) : binaryWordWidth (max a b)≤binaryWordWidth a+binaryWordWidth b := by
  rcases le_total a b with h|h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

theorem ceiling_word (target : ℕ) :
    binaryWordWidth (GeneralPaperPowerCeiling.ceiling target).power≤4+binaryWordWidth target := by
  by_cases ht : target=0
  · subst target
    have he : (GeneralPaperPowerCeiling.ceiling 0).power=1 := by
      rw [GeneralPaperPowerCeiling.ceiling,GeneralPaperPowerCeiling.loop,ite_eq_left (by decide : 0≤1)]
    rw [he]
    decide
  · have hu := GeneralPaperPowerCeiling.ceiling_upper target (by omega)
    have hm := binaryWordWidth_mono hu.le
    have hw := binaryWordWidth_mul 2 target
    have h2 : binaryWordWidth 2=2 := by decide
    omega

theorem ceiling_input_word (target : ℕ) :
    1+binaryWordWidth (2*(target+1))≤binaryWordWidth target+8 := by
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add target 1
  have hm := binaryWordWidth_mul 2 (target+1)
  have h1 : binaryWordWidth 1=1 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  omega

theorem ceiling_depth_word (target : ℕ) :
    binaryWordWidth (GeneralPaperPowerCeiling.ceiling target).doublings≤binaryWordWidth target+1 := by
  have hd := GeneralPaperPowerCeiling.loop_depth target 1 (by decide)
  change (GeneralPaperPowerCeiling.ceiling target).doublings≤binaryWordWidth target at hd
  exact (GeneralPaperInitializerControlCounters.word_le_self _).trans (Nat.add_le_add_right hd 1)

end Blotto.GeneralPaperParameterOperandBounds
