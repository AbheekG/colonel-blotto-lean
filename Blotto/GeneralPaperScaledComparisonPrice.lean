import Blotto.GeneralPaperDyadicComparisonEnvelope

/-! Both scaling products and the final work-field addition are included.
The comparator consumes the two constructed scaled numbers exactly once.
The arithmetic path contains no integer quotient primitive.
-/
namespace Blotto.GeneralPaperScaledComparisonPrice
open GeneralPaperDyadicFloat GeneralPaperDyadicCompare
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def finish (primitive : ℕ → ℕ) (W leftFactor : ℕ) (left : Number)
    (rightFactor : ℕ) (right : Number) (compared : Result × ℕ) : Result × ℕ :=
  (⟨compared.1.answer,compared.1.work+16⟩,compared.2+128*W+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) leftFactor left.mantissa+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) rightFactor right.mantissa+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) compared.1.work 16)

def run (primitive : ℕ → ℕ) (W digits leftFactor : ℕ) (left : Number)
    (rightFactor : ℕ) (right : Number) : Result × ℕ :=
  let scaledLeft := scale leftFactor left
  let scaledRight := scale rightFactor right
  let compared := GeneralPaperDyadicComparisonPrice.run primitive W digits scaledLeft scaledRight
  finish primitive W leftFactor left rightFactor right compared

def arithmetic (digits leftFactor : ℕ) (left : Number) (rightFactor : ℕ) (right : Number) : Result × ℕ :=
  let scaledLeft := scale leftFactor left
  let scaledRight := scale rightFactor right
  let compared := GeneralPaperDyadicComparisonPrice.arithmetic digits scaledLeft scaledRight
  finish (fun _ => 1) 1 leftFactor left rightFactor right compared

theorem data (primitive : ℕ → ℕ) (W digits leftFactor : ℕ) (left : Number)
    (rightFactor : ℕ) (right : Number) :
    (run primitive W digits leftFactor left rightFactor right).1=scaledLE digits leftFactor left rightFactor right := by
  simp only [run,finish,GeneralPaperDyadicComparisonPrice.data,scaledLE]

theorem arithmetic_data (digits leftFactor : ℕ) (left : Number) (rightFactor : ℕ) (right : Number) :
    (arithmetic digits leftFactor left rightFactor right).1=scaledLE digits leftFactor left rightFactor right := by
  simp only [arithmetic,finish,GeneralPaperDyadicComparisonPrice.arithmetic_data,scaledLE]

theorem arithmetic_work (digits leftFactor : ℕ) (left : Number) (rightFactor : ℕ) (right : Number) :
    (arithmetic digits leftFactor left rightFactor right).2≤1024*(digits+1) := by
  have h := GeneralPaperDyadicComparisonPrice.arithmetic_work digits (scale leftFactor left) (scale rightFactor right)
  change (GeneralPaperDyadicComparisonPrice.arithmetic digits (scale leftFactor left) (scale rightFactor right)).2+
    128+(1+1)+(1+1)+(1+1)≤_
  omega

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W digits leftFactor : ℕ) (left : Number)
    (rightFactor : ℕ) (right : Number)
    (hLeftFactor : leftFactor<2^digits) (hRightFactor : rightFactor<2^digits)
    (hLeft : left.mantissa<2^digits) (hRight : right.mantissa<2^digits)
    (hScaledLeft : (scale leftFactor left).mantissa<2^digits)
    (hScaledRight : (scale rightFactor right).mantissa<2^digits) :
    (run primitive W digits leftFactor left rightFactor right).2≤
      4096*(digits+1)*(W+primitive (GeneralPaperDyadicComparisonEnvelope.width digits left right)) := by
  let L := GeneralPaperDyadicComparisonEnvelope.width digits left right
  have h := GeneralPaperDyadicComparisonEnvelope.work primitive hMono W digits
    (scale leftFactor left) (scale rightFactor right) hScaledLeft hScaledRight
  change _≤2048*(digits+1)*(W+primitive L) at h
  have hA := GeneralPaperDyadicComparisonEnvelope.mantissa_word digits leftFactor hLeftFactor
  have hB := GeneralPaperDyadicComparisonEnvelope.mantissa_word digits rightFactor hRightFactor
  have hC := GeneralPaperDyadicComparisonEnvelope.mantissa_word digits left.mantissa hLeft
  have hD := GeneralPaperDyadicComparisonEnvelope.mantissa_word digits right.mantissa hRight
  have hE := GeneralPaperDyadicComparisonEnvelope.mantissa_word digits (leftFactor*left.mantissa) hScaledLeft
  have hF := GeneralPaperDyadicComparisonEnvelope.mantissa_word digits (rightFactor*right.mantissa) hScaledRight
  have hl := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) leftFactor left.mantissa L
    (by dsimp [L,GeneralPaperDyadicComparisonEnvelope.width]; omega)
    (by dsimp [L,GeneralPaperDyadicComparisonEnvelope.width]; omega)
    (by dsimp [L,GeneralPaperDyadicComparisonEnvelope.width]; omega)
  have hr := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) rightFactor right.mantissa L
    (by dsimp [L,GeneralPaperDyadicComparisonEnvelope.width]; omega)
    (by dsimp [L,GeneralPaperDyadicComparisonEnvelope.width]; omega)
    (by dsimp [L,GeneralPaperDyadicComparisonEnvelope.width]; omega)
  let compared := GeneralPaperDyadicComparisonPrice.run primitive W digits (scale leftFactor left) (scale rightFactor right)
  have hw : compared.1.work≤8*digits+26 := by
    dsimp only [compared]
    rw [GeneralPaperDyadicComparisonPrice.data]
    exact le_work _ _ _
  have hWord := GeneralPaperInitializerControlCounters.word_le_self digits
  have hMul := binaryWordWidth_mul 8 digits
  have hAdd := GeneralPaperRayOperandWidthEnvelope.word_add (8*digits) 26
  have hRet := GeneralPaperRayOperandWidthEnvelope.word_add (8*digits+26) 16
  have h8 : binaryWordWidth 8=4 := by decide
  have h26 : binaryWordWidth 26=5 := by decide
  have h16 : binaryWordWidth 16=5 := by decide
  have hW := binaryWordWidth_mono hw
  have hWR := binaryWordWidth_mono (Nat.add_le_add_right hw 16)
  have hm := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) compared.1.work 16 L
    (by dsimp [L,GeneralPaperDyadicComparisonEnvelope.width]; omega)
    (by dsimp [L,GeneralPaperDyadicComparisonEnvelope.width]; omega)
    (by dsimp [L,GeneralPaperDyadicComparisonEnvelope.width]; omega)
  change compared.2+128*W+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) leftFactor left.mantissa+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) rightFactor right.mantissa+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) compared.1.work 16≤
      4096*(digits+1)*(W+primitive L)
  change compared.2≤2048*(digits+1)*(W+primitive L) at h
  nlinarith only [h,hl,hr,hm,Nat.zero_le digits]

end Blotto.GeneralPaperScaledComparisonPrice
