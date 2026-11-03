import Blotto.GeneralPaperActualSourceExponent

/-! Read a stored branch mass or construct a uniform interval mass from
retained unit/precision/height fields. Uniform masses cast/subtract encoded
exponents; no rational power of the interval height is constructed.
-/
namespace Blotto.GeneralPaperMassReadPrice
open GeneralPaperDyadicFloat GeneralPaperIntervalCache
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def width (unit p height : ℕ) : ℕ :=
  64+8*(binaryWordWidth unit+binaryWordWidth p+binaryWordWidth (height+1)+1)

def uniform (primitive : ℕ → ℕ) (W unit p height : ℕ) : Number × ℕ :=
  let h : ℤ := height
  let precision : ℤ := p
  (⟨unit,h-precision⟩,primitive (1+binaryWordWidth unit)+
    primitive (GeneralPaperIntegerPrimitivePrice.word h)+primitive (GeneralPaperIntegerPrimitivePrice.word precision)+
    GeneralPaperIntegerPrimitivePrice.binary primitive (fun a b => a-b) h precision+64*W)

theorem uniform_data (primitive : ℕ → ℕ) (W unit p height : ℕ) :
    (uniform primitive W unit p height).1=GeneralPaperDyadicShift.uniformMass unit p height := rfl

theorem uniform_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W unit p height : ℕ) :
    (uniform primitive W unit p height).2≤5*primitive (width unit p height)+64*W := by
  let L := width unit p height
  have hh := binaryWordWidth_mono (show height≤height+1 by omega)
  have hs := GeneralPaperRayOperandWidthEnvelope.word_add height p
  have hSubAbs : ((height:ℤ)-(p:ℤ)).natAbs≤height+p := by omega
  have hSubW := GeneralPaperIntegerPrimitivePrice.word_bound ((height:ℤ)-(p:ℤ)) (height+p) hSubAbs
  have hH : GeneralPaperIntegerPrimitivePrice.word (height:ℤ)≤L := by
    simp only [GeneralPaperIntegerPrimitivePrice.word,Int.natAbs_natCast]
    dsimp [L,width]
    omega
  have hP : GeneralPaperIntegerPrimitivePrice.word (p:ℤ)≤L := by
    simp only [GeneralPaperIntegerPrimitivePrice.word,Int.natAbs_natCast]
    dsimp [L,width]
    omega
  have hS : GeneralPaperIntegerPrimitivePrice.word ((height:ℤ)-(p:ℤ))≤L := by dsimp [L,width]; omega
  have hU := hMono (show 1+binaryWordWidth unit≤L by dsimp [L,width]; omega)
  have hHC := hMono hH
  have hPC := hMono hP
  have hBinary := GeneralPaperIntegerWordPrice.integer_binary primitive hMono (fun a b => a-b)
    (height:ℤ) (p:ℤ) L hH hP hS
  change primitive (1+binaryWordWidth unit)+primitive (GeneralPaperIntegerPrimitivePrice.word (height:ℤ))+
    primitive (GeneralPaperIntegerPrimitivePrice.word (p:ℤ))+
    GeneralPaperIntegerPrimitivePrice.binary primitive (fun a b => a-b) (height:ℤ) (p:ℤ)+64*W≤5*primitive L+64*W
  omega

def run (primitive : ℕ → ℕ) (W : ℕ) (prepared : GeneralPaperPreparedPowers.Prepared) :
    {height : ℕ} → Node height → Number × ℕ
  | _,.uniform height _ => uniform primitive W prepared.format.unit prepared.format.fractionalBits height
  | _,.branch _ cached _ _ => (cached,16*W)

theorem data (primitive : ℕ → ℕ) (W : ℕ) (prepared : GeneralPaperPreparedPowers.Prepared) {height : ℕ} (n : Node height) :
    (run primitive W prepared n).1=mass prepared n := by cases n <;> rfl

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W : ℕ)
    (prepared : GeneralPaperPreparedPowers.Prepared) {height : ℕ} (n : Node height) :
    (run primitive W prepared n).2≤5*primitive (width prepared.format.unit prepared.format.fractionalBits height)+64*W := by
  cases n with
  | uniform height level => exact uniform_work primitive hMono W _ _ _
  | branch level cached left right => change 16*W≤_; omega

theorem arithmetic_work (prepared : GeneralPaperPreparedPowers.Prepared) {height : ℕ} (n : Node height) :
    (run (fun _ => 1) 1 prepared n).2≤69 := by
  have h := work (fun _ => 1) (fun _ _ _ => Nat.le_refl 1) 1 prepared n
  omega

theorem operand_width (m lambda k Qv height : ℕ) (hHeight : height≤lambda+1) :
    width (GeneralPaperPowerPrecision.prepare lambda k).unit (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits height≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  have hp := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).fractionalBits
  change f.fractionalBits≤128*M at hp
  have hUnit := GeneralPaperParameterOperandBounds.dyadic_word f.fractionalBits
  rw [(GeneralPaperScoreScaleParameters.power_data f.fractionalBits).1,←GeneralPaperPowerPrecision.unit_power lambda k] at hUnit
  change binaryWordWidth f.unit≤1+2*f.fractionalBits at hUnit
  have hPWord := GeneralPaperInitializerControlCounters.word_le_self f.fractionalBits
  have hH := binaryWordWidth_mono (show height+1≤lambda+2 by omega)
  have hLambda := GeneralPaperRayOperandWidthEnvelope.word_add lambda 2
  have hL := binaryWordWidth_mono (show lambda≤lambda+1 by omega)
  have h2 : binaryWordWidth 2=2 := by decide
  have hM : binaryWordWidth (lambda+1)≤M := by dsimp [M,GeneralPaperSourcePreparationSizes.measure]; omega
  have hPos := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  change 128≤M at hPos
  change width f.unit f.fractionalBits height≤1048576*M
  unfold width
  omega

end Blotto.GeneralPaperMassReadPrice
