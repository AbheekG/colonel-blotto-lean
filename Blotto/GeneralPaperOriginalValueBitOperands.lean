import Blotto.GeneralPaperOriginalSourceValueContract

/-! Closed short operands for the actual original-value bit preparation.
Only the first aggregate input retains original rational lengths. These
are erased analysis bounds, never an executable encoding/size census. -/
namespace Blotto.GeneralPaperOriginalValueBitOperands
open GeneralPaperOriginalSourceValuePrice GeneralPaperSummaryArrayExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def logarithm (n k W : ℕ) : ℕ := 128+W+k+binaryWordWidth (n+4)
def operand (n k W : ℕ) : ℕ := 4096*logarithm n k W
def aggregate (n k W S : ℕ) : ℕ := 8*S+16*(n+1)*operand n k W

theorem basics (n k W : ℕ) : 1≤logarithm n k W ∧ W≤operand n k W ∧
    binaryWordWidth k+1≤logarithm n k W ∧ 1≤operand n k W := by
  have hk := Nat.log2_le_self k
  unfold operand logarithm binaryWordWidth
  omega

theorem power_width (n k W : ℕ) : GeneralPaperNatPowerOperands.width 2 k≤operand n k W := by
  have hk := (basics n k W).2.2.1
  have h2 : binaryWordWidth 2=2 := by decide
  unfold GeneralPaperNatPowerOperands.width
  rw [h2]
  unfold operand logarithm at *
  omega

theorem scale_width (n k W c : ℕ) (hc : c≤512) : scaleWidth c n k≤operand n k W := by
  have hC := binaryWordWidth_mono hc
  have hN := binaryWordWidth_mono (show n≤n+4 by omega)
  rw [show binaryWordWidth 512=10 by decide] at hC
  unfold scaleWidth operand logarithm
  omega

theorem rounded_width (n k W c : ℕ) (hc : c≤512) :
    33+9*binaryWordWidth (GeneralPaperValueRoundingPaperContract.scale c n k+n)≤operand n k W := by
  have hC := binaryWordWidth_mono hc
  rw [show binaryWordWidth 512=10 by decide] at hC
  have hN := binaryWordWidth_mono (show n≤n+4 by omega)
  have h0 := binaryWordWidth_mul c n
  have h1 := binaryWordWidth_mul (c*n) (2^k)
  have h2 := GeneralPaperReferenceScaling.word_add (c*n*2^k) n
  have hp : binaryWordWidth (2^k)=k+1 := by simp only [binaryWordWidth,Nat.log2_two_pow]
  rw [hp] at h1
  unfold GeneralPaperValueRoundingPaperContract.scale operand logarithm
  omega

theorem array_word (n k W count : ℕ) (hc : count≤2*n+GeneralPaperLightFieldReduction.representatives k) :
    arrayWord W count≤operand n k W := by
  have hR := GeneralPaperOriginalValueReductionPrice.representatives_word k
  have h0 := binaryWordWidth_mul 2 n
  have h1 := GeneralPaperReferenceScaling.word_add (2*n) (GeneralPaperLightFieldReduction.representatives k)
  have h2 := GeneralPaperReferenceScaling.word_add (2*n+GeneralPaperLightFieldReduction.representatives k) 1
  have h3 := binaryWordWidth_mono (Nat.add_le_add_right hc 1)
  have hN := binaryWordWidth_mono (show n≤n+4 by omega)
  rw [show binaryWordWidth 2=2 by decide] at h0
  rw [show binaryWordWidth 1=1 by decide] at h2
  unfold arrayWord operand logarithm
  omega

theorem first_denominator_word {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    binaryWordWidth (GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1.2≤binaryWordWidth n+k+10 := by
  have h := GeneralPaperOriginalValueReduction.denominator_word true model W k values v hv
  rw [(GeneralPaperOriginalValueReduction.retained true model W k values).2] at h
  exact h

theorem scan_width (n k W Q : ℕ) (hQ : binaryWordWidth Q≤binaryWordWidth n+k+10) :
    1+binaryWordWidth (GeneralPaperLightFieldScanPrice.magnitude (GeneralPaperLightFieldScanContract.multiplier k) Q)≤operand n k W := by
  have h0 := binaryWordWidth_mul 10 (2^k)
  have h1 := GeneralPaperReferenceScaling.word_add (10*2^k) 1
  have h2 := GeneralPaperReferenceScaling.word_add Q 1
  have h3 := binaryWordWidth_mul (10*2^k+1) (Q+1)
  have hN := binaryWordWidth_mono (show n≤n+4 by omega)
  rw [show binaryWordWidth 10=4 by decide,show binaryWordWidth (2^k)=k+1 by simp only [binaryWordWidth,Nat.log2_two_pow]] at h0
  rw [show binaryWordWidth 1=1 by decide] at h1 h2
  unfold GeneralPaperLightFieldScanPrice.magnitude GeneralPaperLightFieldScanContract.multiplier operand logarithm
  omega

theorem reduced_width (n k W Q : ℕ) (hQ : binaryWordWidth Q≤binaryWordWidth n+k+10) :
    GeneralPaperReducedValueArrayPrice.width Q (GeneralPaperLightFieldReduction.representatives k)≤operand n k W := by
  have hR := GeneralPaperOriginalValueReductionPrice.representatives_word k
  have hN := binaryWordWidth_mono (show n≤n+4 by omega)
  unfold GeneralPaperReducedValueArrayPrice.width operand logarithm
  rw [hR]
  omega

theorem second_width (n k W : ℕ) : reducedWidth n k≤operand n k W := by
  have hN := binaryWordWidth_mono (show n≤n+4 by omega)
  unfold reducedWidth operand logarithm
  omega

theorem first_aggregate {n : ℕ} (k W c : ℕ) (hc : c≤512) (values : FixedArrayTable n ℚ) :
    GeneralPaperValueRoundingInputPrice.size (GeneralPaperValueRoundingPaperContract.scale c n k) values≤
      aggregate n k W (GeneralPaperValueRoundingInputPrice.inputSize values) := by
  have h := Nat.mul_le_mul_left n (rounded_width n k W c hc)
  unfold GeneralPaperValueRoundingInputPrice.size aggregate
  nlinarith only [h,Nat.zero_le (operand n k W)]

theorem second_aggregate (n k W S : ℕ) : secondSize n k≤aggregate n k W S := by
  have h0 := Nat.mul_le_mul_left (8*n) (second_width n k W)
  have h1 := Nat.mul_le_mul_left n (rounded_width n k W 512 le_rfl)
  unfold secondSize aggregate
  nlinarith only [h0,h1,Nat.zero_le (operand n k W),Nat.zero_le S]

end Blotto.GeneralPaperOriginalValueBitOperands
