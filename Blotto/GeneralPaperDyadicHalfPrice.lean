import Blotto.GeneralPaperFreshMassPrice

/-! Virtual halving changes an encoded exponent once. Zero tests, signed
arithmetic and result writes are charged without constructing a denominator.
-/
namespace Blotto.GeneralPaperDyadicHalfPrice
open GeneralPaperDyadicFloat
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def width (unit : ℕ) (x : Number) : ℕ := 64+8*(binaryWordWidth unit+binaryWordWidth x.exponent.natAbs+1)

def run (primitive : ℕ → ℕ) (W : ℕ) (x : Number) : Number × ℕ :=
  let test := GeneralPaperIntegerWordPrice.compare primitive x.mantissa 0
  if x.mantissa=0 then (zero,test+32*W) else
    (⟨x.mantissa,x.exponent+(-1)⟩,test+GeneralPaperIntegerPrimitivePrice.binary primitive (fun a b => a+b) x.exponent (-1)+32*W)

theorem data (primitive : ℕ → ℕ) (W : ℕ) (x : Number) :
    (run primitive W x).1=GeneralPaperDyadicShift.shift x (-1) := by
  unfold run GeneralPaperDyadicShift.shift
  split <;> rfl

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W unit : ℕ) (x : Number) (hNormal : Normal unit x) :
    (run primitive W x).2≤3*primitive (width unit x)+32*W := by
  let L := width unit x
  have hMantissa : x.mantissa≤2*unit := by rcases hNormal with h|h <;> omega
  have hm := binaryWordWidth_mono hMantissa
  have hMul := binaryWordWidth_mul 2 unit
  have h2 : binaryWordWidth 2=2 := by decide
  have h0 : binaryWordWidth 0=1 := by decide
  have h1 : binaryWordWidth 1=1 := by decide
  have hTest := GeneralPaperIntegerWordPrice.compare_le primitive hMono x.mantissa 0 L
    (by dsimp [L,width]; omega) (by dsimp [L,width]; omega)
  have hAbs : (x.exponent+(-1)).natAbs≤x.exponent.natAbs+1 := by omega
  have hAdd := GeneralPaperRayOperandWidthEnvelope.word_add x.exponent.natAbs 1
  have hSum := GeneralPaperIntegerPrimitivePrice.word_bound (x.exponent+(-1)) (x.exponent.natAbs+1) hAbs
  have hE : GeneralPaperIntegerPrimitivePrice.word x.exponent≤L := by
    dsimp [L,width,GeneralPaperIntegerPrimitivePrice.word]
    omega
  have hOne : GeneralPaperIntegerPrimitivePrice.word (-1)≤L := by
    change 1+binaryWordWidth 1≤L
    dsimp [L,width]
    omega
  have hS : GeneralPaperIntegerPrimitivePrice.word (x.exponent+(-1))≤L := by dsimp [L,width]; omega
  have hBinary := GeneralPaperIntegerWordPrice.integer_binary primitive hMono (fun a b => a+b) x.exponent (-1) L hE hOne hS
  unfold run
  dsimp only
  split <;> change _≤3*primitive L+32*W <;> omega

theorem arithmetic_work (x : Number) : (run (fun _ => 1) 1 x).2≤35 := by
  unfold run GeneralPaperIntegerWordPrice.compare GeneralPaperIntegerPrimitivePrice.binary
  dsimp only
  split <;> omega

theorem operand_width (m lambda k Qv : ℕ) (x : Number)
    (h : x.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k) :
    width (GeneralPaperPowerPrecision.prepare lambda k).unit x≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  have hExp := (binaryWordWidth_mono h).trans (GeneralPaperStoredExponentEnvelope.word_bound m lambda k Qv)
  have hp := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).fractionalBits
  change f.fractionalBits≤128*M at hp
  have hu := GeneralPaperParameterOperandBounds.dyadic_word f.fractionalBits
  rw [(GeneralPaperScoreScaleParameters.power_data f.fractionalBits).1,←GeneralPaperPowerPrecision.unit_power lambda k] at hu
  change binaryWordWidth f.unit≤1+2*f.fractionalBits at hu
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  change 128≤M at hM
  change binaryWordWidth x.exponent.natAbs≤256*M at hExp
  change width f.unit x≤1048576*M
  unfold width
  omega

end Blotto.GeneralPaperDyadicHalfPrice
