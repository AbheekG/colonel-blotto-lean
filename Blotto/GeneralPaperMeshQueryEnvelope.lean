import Blotto.GeneralPaperMeshQueryWork

/-! Retained source records and cached total words discharge all mesh-query
premises. The global reference word W is kept separate from these operand
words. Computing 30+k is charged at each native query.
-/
namespace Blotto.GeneralPaperMeshQueryEnvelope
open GeneralPaperMeshQueryExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem mesh_word (m lambda k Qv : ℕ) :
    1+binaryWordWidth (GeneralPaperSourceParameters.prepare k).meshDenominator≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have h := GeneralPaperNatPowerOperands.power_width 2 (29+k)
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2,←(GeneralPaperSourceParameters.data k).2.2.2.2.1] at h
  have hk := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  unfold GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

theorem depth_word (m lambda k Qv : ℕ) :
    1+binaryWordWidth (30+k)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have h := GeneralPaperInitializerControlCounters.word_le_self (30+k)
  have hk := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  unfold GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

theorem depth_work (price : ℕ → ℕ) (hMono : Monotone price) (m lambda k Qv : ℕ) :
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) 30 k≤
      2*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) := by
  exact (GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) 30 k (30+k)
    (by omega) (by omega) (Nat.le_refl _)).trans (Nat.mul_le_mul_left 2 (hMono (depth_word m lambda k Qv)))

theorem quotient_width (m lambda k Qv : ℕ) :
    let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
    GeneralPaperCompleteQuotientPrice.width (2*H) H (30+k)≤64*H := by
  have hk := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  unfold GeneralPaperCompleteQuotientPrice.width GeneralPaperBoundedQuotient.heightBudget
    GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

def profile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  512*(k+31)*(W+price (64*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv))

def arithmeticProfile (k : ℕ) : ℕ := 80*(k+31)+172

theorem combine (k W P core depth : ℕ) (hCore : core≤256*(k+31)*(W+P)) (hDepth : depth≤2*P) :
    core+depth+32*W≤512*(k+31)*(W+P) := by
  nlinarith only [hCore,hDepth,Nat.zero_le (k*W),Nat.zero_le (k*P)]

theorem selected_work (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv mesh numerator total : ℕ)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hTotal : 0<total) (hNumerator : numerator≤total)
    (hWord : 1+binaryWordWidth total≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) :
    (selected price W k mesh numerator total).2≤profile price W m lambda k Qv := by
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  change 1+binaryWordWidth total≤H at hWord
  have hm : binaryWordWidth mesh≤H := by rw [hMesh]; have h := mesh_word m lambda k Qv; omega
  have ht : binaryWordWidth total≤H := by omega
  have hc := GeneralPaperMeshQueryWork.work price hMono W mesh (30+k) numerator total H hTotal hNumerator
    (by rw [hMesh]; exact GeneralPaperCDFMesh.selected_depth k) hm ht
  have hPrice := hMono (quotient_width m lambda k Qv)
  have hCore := hc.trans (Nat.mul_le_mul_left (256*(30+k+1)) (Nat.add_le_add_left hPrice W))
  have hd := (depth_work price hMono m lambda k Qv).trans
    (Nat.mul_le_mul_left 2 (hMono (show H≤64*H by omega)))
  apply combine k W (price (64*H)) _ _ _ hd
  change (run price W mesh (30+k) numerator total).2≤256*(30+k+1)*(W+price (64*H)) at hCore
  exact hCore.trans_eq (by rw [show 30+k+1=k+31 by omega])

end Blotto.GeneralPaperMeshQueryEnvelope
