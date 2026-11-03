import Blotto.GeneralPaperRoundFieldsPrice

/-! Native option profits use stored integer weights, the retained horizon
and mesh counts. Raw products are bounded before reduction. Prepared source
records derive the complete encoded operand word, including zero weights.
-/
namespace Blotto.GeneralPaperNativeProfitOperands
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def cap (T Qv mesh : ℕ) : ℕ := 8*(T+1)*(Qv+1)*(mesh+1)+64

theorem cap_large (T Qv mesh : ℕ) :
    4*T*Qv*mesh≤cap T Qv mesh ∧ 2*T*Qv≤cap T Qv mesh ∧
    2*T≤cap T Qv mesh ∧ 2*mesh≤cap T Qv mesh ∧ Qv≤cap T Qv mesh ∧ 2≤cap T Qv mesh := by
  unfold cap
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;>
    nlinarith only [Nat.zero_le (T*Qv*mesh),Nat.zero_le (T*Qv),Nat.zero_le (T*mesh),Nat.zero_le (Qv*mesh),
      Nat.zero_le T,Nat.zero_le Qv,Nat.zero_le mesh]

theorem coefficient_bound (T Qv mesh weight : ℕ) (hWeight : weight≤Qv) :
    2*T*weight≤2*T*Qv ∧ 2*T*weight≤cap T Qv mesh := by
  have h := Nat.mul_le_mul_left (2*T) hWeight
  exact ⟨h,h.trans (cap_large T Qv mesh).2.1⟩

theorem profit_bound (T Qv mesh weight positive negative : ℕ) (hWeight : weight≤Qv) (hPositive : positive≤mesh) :
    2*T*weight*(mesh+positive-negative)≤4*T*Qv*mesh := by
  have ha : mesh+positive-negative≤2*mesh := by omega
  have h := Nat.mul_le_mul (Nat.mul_le_mul_left (2*T) hWeight) ha
  exact h.trans_eq (by ring)

theorem operand_word (m lambda k Qv : ℕ) :
    1+binaryWordWidth (cap (GeneralPaperTrajectoryParameters.prepare lambda k).rows Qv
      (GeneralPaperSourceParameters.prepare k).meshDenominator)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  let T := (GeneralPaperTrajectoryParameters.prepare lambda k).rows
  let mesh := (GeneralPaperSourceParameters.prepare k).meshDenominator
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  have ht := (GeneralPaperSourcePreparationSizes.sizes m lambda k Qv).rows
  change binaryWordWidth T≤8*M at ht
  have hT1 := GeneralPaperRayOperandWidthEnvelope.word_add T 1
  have hQ : binaryWordWidth (Qv+1)≤M := by unfold M GeneralPaperSourcePreparationSizes.measure; omega
  have hm := GeneralPaperNatPowerOperands.power_width 2 (29+k)
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2,←(GeneralPaperSourceParameters.data k).2.2.2.2.1] at hm
  change binaryWordWidth mesh≤1+(29+k)*2 at hm
  have hm1 := GeneralPaperRayOperandWidthEnvelope.word_add mesh 1
  have ha := binaryWordWidth_mul 8 (T+1)
  have hb := binaryWordWidth_mul (8*(T+1)) (Qv+1)
  have hc := binaryWordWidth_mul (8*(T+1)*(Qv+1)) (mesh+1)
  have hd := GeneralPaperRayOperandWidthEnvelope.word_add (8*(T+1)*(Qv+1)*(mesh+1)) 64
  have h1 : binaryWordWidth 1=1 := by decide
  have h8 : binaryWordWidth 8=4 := by decide
  have h64 : binaryWordWidth 64=7 := by decide
  have hk := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  change k+128≤M at hk
  change 128≤M at hM
  change 1+binaryWordWidth (8*(T+1)*(Qv+1)*(mesh+1)+64)≤1048576*M
  omega

end Blotto.GeneralPaperNativeProfitOperands
