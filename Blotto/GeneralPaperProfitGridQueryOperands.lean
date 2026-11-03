import Blotto.GeneralPaperProfitGridRoundPrice
import Blotto.GeneralPaperProfitGridEnvelope

/-! The actual cached grid and the native profit cap supply query bounds.
The common word follows from retained constructor records. No maximum scan,
parameter constructor, scaled-grid rebuild or operand census executes. -/
namespace Blotto.GeneralPaperProfitGridQueryOperands
open GeneralPaperProfitGridPrepare GeneralPaperProfitGridPoints
set_option autoImplicit false
set_option maxHeartbeats 6000000

def cap (q F : ℕ) : ℕ := 16*(q+1)*(F+1)+64

theorem cap_large (q F : ℕ) :
    2*q≤cap q F ∧ F≤cap q F ∧ 2*q*F+1≤cap q F ∧ 4*F+1≤cap q F := by
  unfold cap
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [Nat.zero_le q,Nat.zero_le F,Nat.zero_le (q*F)]

theorem leaf_operands (q w B numerator : ℕ) (hNum : numerator≤2*q) :
    let grid := prepare q w B
    let V := cap q (denominator w B)
    numerator≤V ∧ grid.profitDenominator≤V ∧ numerator*grid.profitDenominator+1≤V ∧
      ∀ i,grid.leafNumerators.read i≤V := by
  have h := cap_large q (denominator w B)
  refine ⟨hNum.trans h.1,h.2.1,?_,?_⟩
  · exact (Nat.add_le_add_right (Nat.mul_le_mul_right (denominator w B) hNum) 1).trans h.2.2.1
  · intro i
    rw [scaled_read]
    have hv := Nat.mul_le_mul_left q (numerator_bound q w B i)
    have hc := h.2.2.1
    nlinarith only [hv,hc]

theorem merge_operands (q w B : ℕ) (i j : Fin (prepare q w B).size) :
    let grid := prepare q w B
    let V := cap q (denominator w B)
    grid.numerators.read i+grid.numerators.read j+1≤V ∧ ∀ a,grid.numerators.read a≤V := by
  have h := (cap_large q (denominator w B)).2.2.2
  have hi := numerator_bound q w B i
  have hj := numerator_bound q w B j
  refine ⟨by omega,?_⟩
  intro a
  have ha := numerator_bound q w B a
  omega

theorem depth_bound (q w B : ℕ) :
    (prepare q w B).depth≤binaryWordWidth (GeneralPaperProfitOrderPrice.capacity w B) := by
  have h := GeneralPaperPowerCeiling.loop_depth ((ordered w B).length+1) 1 (by decide)
  change (prepare q w B).depth≤binaryWordWidth ((prepare q w B).size+1) at h
  apply h.trans
  apply binaryWordWidth_mono
  have hs := size_bound q w B
  unfold GeneralPaperProfitOrderPrice.capacity
  nlinarith only [hs,Nat.zero_le B]

theorem source_word (m lambda k Qv : ℕ) :
    let p := GeneralPaperProfitParameters.parameters m lambda k Qv
    GeneralPaperRankOperands.width (prepare p.qProf p.width p.exponent).depth
      (cap p.qProf (denominator p.width p.exponent))≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  let F := denominator p.width p.exponent
  have hs := GeneralPaperProfitGridEnvelope.sizes m lambda k Qv
  have hq := hs.q
  have hw := hs.width
  have hb := hs.exponent
  have hc := hs.capacity
  change binaryWordWidth p.qProf≤32*M at hq
  change binaryWordWidth (p.width+1)≤16*M at hw
  change p.exponent≤32*M at hb
  change binaryWordWidth (GeneralPaperProfitOrderPrice.capacity p.width p.exponent)≤64*M at hc
  have hd := (depth_bound p.qProf p.width p.exponent).trans hc
  have hp := GeneralPaperNatPowerOperands.power_width 2 p.exponent
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hp
  have hw0 := binaryWordWidth_mono (show p.width≤p.width+1 by omega)
  have hF := binaryWordWidth_mul (2^p.exponent) p.width
  change binaryWordWidth F≤_ at hF
  have hF1 := GeneralPaperRayOperandWidthEnvelope.word_add F 1
  have hq1 := GeneralPaperRayOperandWidthEnvelope.word_add p.qProf 1
  have ha := binaryWordWidth_mul 16 (p.qProf+1)
  have hm := binaryWordWidth_mul (16*(p.qProf+1)) (F+1)
  have hx := GeneralPaperRayOperandWidthEnvelope.word_add (16*(p.qProf+1)*(F+1)) 64
  have hy := GeneralPaperRayOperandWidthEnvelope.word_add (16*(p.qProf+1)*(F+1)+64) 1
  have h1 : binaryWordWidth 1=1 := by decide
  have h16 : binaryWordWidth 16=5 := by decide
  have h64 : binaryWordWidth 64=7 := by decide
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  change 128≤M at hM
  change 256+32*((prepare p.qProf p.width p.exponent).depth+binaryWordWidth (16*(p.qProf+1)*(F+1)+64+1))≤1048576*M
  omega

end Blotto.GeneralPaperProfitGridQueryOperands
