import Blotto.PlayerSpecificEnclosureExecution

/-! Exact integer separation denominator from actual enclosure, measured
squarefree/certificate widths and the actual right-certificate length. -/
namespace Blotto.PlayerSpecificSeparationExecution
open PlayerSpecificNaturalExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run (model : RationalCostModel) (M A B k : ℕ) : ℕ×ℕ :=
  let squarefreePower := power model 2 A
  let certificatePower := power model 2 B
  let triple := binary model (fun a b => a*b) 3 M
  let derivativeFactor := binary model (fun a b => a+b) 1 triple.1
  let derivative := binary model (fun a b => a*b) squarefreePower.1 derivativeFactor.1
  let certificateFactor := binary model (fun a b => a+b) 1 M
  let certificateGrowth := power model certificateFactor.1 k
  let bezout := binary model (fun a b => a*b) certificatePower.1 certificateGrowth.1
  let product := binary model (fun a b => a*b) derivative.1 bezout.1
  (product.1,squarefreePower.2+certificatePower.2+triple.2+derivativeFactor.2+derivative.2+
    certificateFactor.2+certificateGrowth.2+bezout.2+product.2+
    32*(5+binaryWordWidth M+binaryWordWidth A+binaryWordWidth B+binaryWordWidth k+binaryWordWidth product.1))

theorem value (model : RationalCostModel) (M A B k : ℕ) :
    (run model M A B k).1=(2^A*(1+3*M))*(2^B*(1+M)^k) := by
  simp only [run,binary,power_value]

def size (M A B : ℕ) : ℕ := binaryWordWidth M+A+B+32
def width (M A B : ℕ) : ℕ := 512*size M A B

theorem words (M A B k : ℕ) (hk : k≤17) :
    binaryWordWidth (1+M)≤binaryWordWidth M+2 ∧
    binaryWordWidth (1+3*M)≤binaryWordWidth M+4 ∧
    binaryWordWidth ((2^A*(1+3*M))*(2^B*(1+M)^k))≤20*size M A B := by
  have hOne : binaryWordWidth 1=1 := by decide
  have hThree : binaryWordWidth 3=2 := by decide
  have h1:=GeneralPaperRayOperandWidthEnvelope.word_add 1 M
  have h3:=binaryWordWidth_mul 3 M
  have h13:=GeneralPaperRayOperandWidthEnvelope.word_add 1 (3*M)
  have hp:=GeneralPaperNatPowerOperands.power_width (1+M) k
  have hm:=Nat.mul_le_mul_left k (by omega : binaryWordWidth (1+M)≤binaryWordWidth M+2)
  have hc:=Nat.mul_le_mul_right (binaryWordWidth M+2) hk
  have hd:=binaryWordWidth_mul (2^A) (1+3*M)
  have hb:=binaryWordWidth_mul (2^B) ((1+M)^k)
  have ht:=binaryWordWidth_mul (2^A*(1+3*M)) (2^B*(1+M)^k)
  rw [PlayerSpecificIsolationDepthHeight.two_power_width] at hd hb
  unfold size
  omega

end Blotto.PlayerSpecificSeparationExecution
