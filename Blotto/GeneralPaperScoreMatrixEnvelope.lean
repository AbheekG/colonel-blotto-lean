import Blotto.GeneralPaperSourceScoreHeights

/-! One common width prices the complete stored score matrix. Value input
precision, bounded-floor depth, label width and source anchor height all
remain visible. No per-entry floor or arithmetic callback oracle is used.
-/
namespace Blotto.GeneralPaperScoreMatrixEnvelope
open GeneralPaperScoreMatrixBits
set_option autoImplicit false
set_option maxHeartbeats 5000000

def width (V A w K : ℕ) : ℕ := 1+2*(V+3*w+2*binaryWordWidth K+A+8)

theorem component_widths (V A w K : ℕ) :
    1+2*GeneralPaperScoreArgumentBits.height V w K≤width V A w K ∧
    1+2*GeneralPaperBoundedQuotient.heightBudget (GeneralPaperScoreArgumentBits.height V w K) 1 w≤width V A w K ∧
    1+2*A≤width V A w K := by
  unfold width GeneralPaperScoreArgumentBits.height GeneralPaperBoundedQuotient.heightBudget
  omega

theorem entry_profile (model : RationalCostModel) (W V A w K : ℕ) :
    entryProfile model W V A w K≤256*(w+1)*(W+model.rat (width V A w K)) := by
  obtain ⟨ha,hb,hc⟩ := component_widths V A w K
  have hpa := model.monotone ha
  have hpb := model.monotone hb
  have hpc := model.monotone hc
  unfold entryProfile scoreProfile GeneralPaperScoreArgumentBits.argumentProfile GeneralPaperBoundedQuotient.bitProfile
  nlinarith only [hpa,hpb,hpc,Nat.zero_le (w*W),Nat.zero_le (w*model.rat (width V A w K))]

theorem matrix_profile (model : RationalCostModel) (W V A w m K : ℕ) :
    matrixProfile model W V A w m K≤512*(m+1)*(K+1)*(w+1)*(W+model.rat (width V A w K)) := by
  let P := (w+1)*(W+model.rat (width V A w K))
  have hW : W≤P := by
    dsimp only [P]
    nlinarith only [Nat.zero_le (w*W),Nat.zero_le (w*model.rat (width V A w K))]
  have he : entryProfile model W V A w K≤256*P := by
    simpa only [P,Nat.mul_assoc] using entry_profile model W V A w K
  have hField : fieldProfile model W V A w K≤320*(K+1)*P := by
    have hh := Nat.mul_le_mul_left K he
    have hw := Nat.mul_le_mul_left (44*(K+1)) hW
    unfold fieldProfile
    nlinarith only [hh,hw,Nat.zero_le (K*P)]
  have hm := Nat.mul_le_mul_left m hField
  have hw := Nat.mul_le_mul_left (44*(m+1)) hW
  have hp : P≤(K+1)*P := by nlinarith only [Nat.zero_le (K*P)]
  have hs := Nat.mul_le_mul_left (44*(m+1)) hp
  calc
    _ ≤ 512*(m+1)*(K+1)*P := by unfold matrixProfile; nlinarith only [hm,hw,hs,Nat.zero_le (m*((K+1)*P))]
    _ = _ := by dsimp only [P]; ring

theorem matrix_data_native {T m K : ℕ} (model : RationalCostModel) (W w : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ)
    (hK : 0<K) (hCap : S<2^w) :
    (matrixRun model W w dict v S).1=(GeneralPaperScoreMatrixWork.matrixRun w dict v S).1 := by
  rw [matrix_data model W w dict v S hK hCap,GeneralPaperScoreMatrixWork.matrix_data w dict v S hK hCap]

end Blotto.GeneralPaperScoreMatrixEnvelope
