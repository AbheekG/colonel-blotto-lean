import Blotto.GeneralPaperLocalPowerNumerators
import Blotto.GeneralPaperStoredExponentEnvelope

/-! Local powers use a common integer denominator. Conversion compares one
encoded exponent and, in the endpoint branch, doubles the mantissa. It never
materializes a rational power or constructs a denominator from that exponent.
-/
namespace Blotto.GeneralPaperLocalNumeratorPrice
open GeneralPaperDyadicFloat
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def width (unit p : ℕ) (x : Number) : ℕ :=
  64+8*(binaryWordWidth unit+binaryWordWidth p+binaryWordWidth x.exponent.natAbs)

def run (price : ℕ → ℕ) (W _unit p : ℕ) (x : Number) : ℕ × ℕ :=
  let precision : ℤ := p
  let target := -precision
  let same := x.exponent=target
  (if same then 2*x.mantissa else x.mantissa,
    price (GeneralPaperIntegerPrimitivePrice.word precision)+
    GeneralPaperIntegerPrimitivePrice.unary price (fun z => -z) precision+
    price (max (GeneralPaperIntegerPrimitivePrice.word x.exponent)
      (GeneralPaperIntegerPrimitivePrice.word target))+
    (if same then GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 x.mantissa else 0)+64*W)

theorem data (price : ℕ → ℕ) (W unit p : ℕ) (x : Number) :
    (run price W unit p x).1=GeneralPaperLocalPowerNumerators.numerator unit p x := rfl

theorem bound (unit p : ℕ) (x : Number) (hNormal : Normal unit x) :
    GeneralPaperLocalPowerNumerators.numerator unit p x≤4*unit := by
  have hm : x.mantissa≤2*unit := by rcases hNormal with h|h <;> omega
  unfold GeneralPaperLocalPowerNumerators.numerator
  split <;> omega

theorem natural_word (unit p : ℕ) (x : Number) :
    1+binaryWordWidth (4*unit+2)≤width unit p x := by
  have h4 := binaryWordWidth_mul 4 unit
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (4*unit) 2
  have hFour : binaryWordWidth 4=3 := by decide
  have hTwo : binaryWordWidth 2=2 := by decide
  unfold width
  omega

theorem work (price : ℕ → ℕ) (hMono : Monotone price) (W unit p : ℕ) (x : Number)
    (hNormal : Normal unit x) : (run price W unit p x).2≤6*price (width unit p x)+64*W := by
  let L := width unit p x
  have hp : GeneralPaperIntegerPrimitivePrice.word (p:ℤ)≤L := by
    simp only [GeneralPaperIntegerPrimitivePrice.word,Int.natAbs_natCast]
    dsimp [L,width]; omega
  have hn : GeneralPaperIntegerPrimitivePrice.word (-(p:ℤ))≤L := by
    simpa only [GeneralPaperIntegerPrimitivePrice.word,Int.natAbs_neg,Int.natAbs_natCast] using hp
  have hx : GeneralPaperIntegerPrimitivePrice.word x.exponent≤L := by
    unfold GeneralPaperIntegerPrimitivePrice.word
    dsimp [L,width]; omega
  have hm : x.mantissa≤2*unit := by rcases hNormal with h|h <;> omega
  have hN := natural_word unit p x
  have hDouble := (GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a*b) 2 x.mantissa
    (4*unit+2) (by omega) (by omega) (by omega)).trans (Nat.mul_le_mul_left 2 (hMono hN))
  have hCast := hMono hp
  have hNeg : GeneralPaperIntegerPrimitivePrice.unary price (fun z => -z) (p:ℤ)≤2*price L := by
    change price (GeneralPaperIntegerPrimitivePrice.word (p:ℤ))+
      price (GeneralPaperIntegerPrimitivePrice.word (-(p:ℤ)))≤2*price L
    have h1 := hMono hp
    have h2 := hMono hn
    omega
  have hCompare := hMono (max_le hx hn)
  dsimp only [L] at hCast hNeg hCompare
  change price (GeneralPaperIntegerPrimitivePrice.word (p:ℤ))+
    GeneralPaperIntegerPrimitivePrice.unary price (fun z => -z) (p:ℤ)+
    price (max (GeneralPaperIntegerPrimitivePrice.word x.exponent) (GeneralPaperIntegerPrimitivePrice.word (-(p:ℤ))))+
    (if x.exponent=-(p:ℤ) then GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 x.mantissa else 0)+64*W≤_
  split <;> omega

theorem operand_width (m lambda k Qv : ℕ) (x : Number)
    (hExp : x.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k) :
    width (GeneralPaperPowerPrecision.prepare lambda k).unit
      (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits x≤
        GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  have he := (binaryWordWidth_mono hExp).trans (GeneralPaperStoredExponentEnvelope.word_bound m lambda k Qv)
  have hp := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).fractionalBits
  change f.fractionalBits≤128*M at hp
  have hw := GeneralPaperInitializerControlCounters.word_le_self f.fractionalBits
  have hu := GeneralPaperParameterOperandBounds.dyadic_word f.fractionalBits
  rw [(GeneralPaperScoreScaleParameters.power_data f.fractionalBits).1,←GeneralPaperPowerPrecision.unit_power lambda k] at hu
  change binaryWordWidth f.unit≤1+2*f.fractionalBits at hu
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  change 128≤M at hM
  change binaryWordWidth x.exponent.natAbs≤256*M at he
  change width f.unit f.fractionalBits x≤1048576*M
  unfold width
  omega

theorem arithmetic_work (unit p : ℕ) (x : Number) (hNormal : Normal unit x) :
    (run (fun _ => 1) 1 unit p x).2≤70 := by
  exact work (fun _ => 1) (fun _ _ _ => Nat.le_refl 1) 1 unit p x hNormal

end Blotto.GeneralPaperLocalNumeratorPrice
