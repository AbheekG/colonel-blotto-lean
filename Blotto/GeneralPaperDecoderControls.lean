import Blotto.GeneralPaperActualCataloguePartition

/-! Decoder values use the actual dyadic alphabet's full code word.
The reference/control word has a derived logarithmic metadata component;
W remains the separate global-address contribution until the final join.
-/
namespace Blotto.GeneralPaperDecoderControls
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 6000000

def controlWord (W lambda : ℕ) : ℕ := W+128+8*binaryWordWidth (lambda+3)
def operandWidth (lambda : ℕ) : ℕ := 512+64*lambda
def metadataCap (lambda : ℕ) : ℕ := 8192*(lambda+1)+8192

theorem control_positive (W lambda : ℕ) : 1≤controlWord W lambda := by unfold controlWord; omega

theorem cf_control (W lambda : ℕ) : GeneralPaperCFControlWords.width lambda≤controlWord W lambda := by
  have h := binaryWordWidth_mono (show lambda+1≤lambda+3 by omega)
  unfold controlWord GeneralPaperCFControlWords.width
  omega

theorem quotient_control (W lambda : ℕ) :
    GeneralPaperQuotientRegisterSpace.counterWord (lambda+2)≤controlWord W lambda := by
  unfold GeneralPaperQuotientRegisterSpace.counterWord controlWord
  change 32+binaryWordWidth (lambda+3)≤W+128+8*binaryWordWidth (lambda+3)
  omega

theorem code_word (a : Alphabet) (code : ℕ) (hCode : code≤8*a.C) :
    1+binaryWordWidth code≤operandWidth a.lambda := by
  have hp := GeneralPaperNatPowerOperands.power_width 2 a.lambda
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hp
  have h := binaryWordWidth_mono (hCode.trans_eq a.dyadic)
  unfold operandWidth
  omega

theorem order_le_scale (a : Alphabet) : a.D≤a.C := by
  have hD := a.orderPositive
  have hSq := a.separated
  have h := Nat.mul_le_mul_left a.D (show 1≤a.D by omega)
  nlinarith only [h,hSq]

theorem cf_width (a : Alphabet) : GeneralPaperCFOperandPrice.width a.lambda a.D≤operandWidth a.lambda := by
  have hp := GeneralPaperNatPowerOperands.power_width 2 a.lambda
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hp
  have hC := binaryWordWidth_mono (show a.C≤2^a.lambda by rw [←a.dyadic]; omega)
  have hd := binaryWordWidth_mono (order_le_scale a)
  unfold GeneralPaperCFOperandPrice.width operandWidth
  omega

theorem metadata_word (lambda value : ℕ) (hValue : value≤metadataCap lambda) :
    1+binaryWordWidth value≤operandWidth lambda := by
  have hm := binaryWordWidth_mul 8192 (lambda+1)
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (8192*(lambda+1)) 8192
  have hc : binaryWordWidth 8192=14 := by decide
  have hv := binaryWordWidth_mono hValue
  have hl := GeneralPaperInitializerControlCounters.word_le_self (lambda+1)
  unfold metadataCap at hv
  unfold operandWidth
  omega

theorem metadata_binary (primitive : ℕ → ℕ) (hMono : Monotone primitive) (lambda : ℕ)
    (op : ℕ → ℕ → ℕ) (a b : ℕ) (ha : a≤metadataCap lambda) (hb : b≤metadataCap lambda)
    (hc : op a b≤metadataCap lambda) :
    GeneralPaperNaturalPrimitivePrice.binary primitive op a b≤2*primitive (operandWidth lambda) :=
  (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono op a b (metadataCap lambda) ha hb hc).trans
    (Nat.mul_le_mul_left 2 (hMono (metadata_word lambda (metadataCap lambda) (Nat.le_refl _))))

end Blotto.GeneralPaperDecoderControls
