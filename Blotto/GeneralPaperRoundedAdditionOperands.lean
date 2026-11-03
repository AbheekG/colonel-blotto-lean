import Blotto.GeneralPaperRoundedAdditionExecution

/-! All near-addition integer operands fit a precision-sized word,
including the sum before normalization. The magnitude and word envelopes
are proof quantities, not an extra encoding or calibration pass.
-/
namespace Blotto.GeneralPaperRoundedAdditionOperands
open GeneralPaperDyadicFloat GeneralPaperRoundedAdditionExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def magnitude (unit p : ℕ) : ℕ := 32*unit*unit+256*(p+1)+256

def width (p : ℕ) (high low : Number) : ℕ :=
  256+16*(p+binaryWordWidth high.exponent.natAbs+binaryWordWidth low.exponent.natAbs)

theorem natural_word (unit p : ℕ) (hPower : unit=2^p) :
    1+binaryWordWidth (magnitude unit p)≤256+16*p := by
  have hu : binaryWordWidth unit≤1+2*p := by
    rw [hPower]
    simpa only [show binaryWordWidth 2=2 by decide,Nat.mul_comm] using GeneralPaperNatPowerOperands.power_width 2 p
  have ha := binaryWordWidth_mul 32 unit
  have hb := binaryWordWidth_mul (32*unit) unit
  have hc := GeneralPaperRayOperandWidthEnvelope.word_add p 1
  have hd := binaryWordWidth_mul 256 (p+1)
  have he := GeneralPaperRayOperandWidthEnvelope.word_add (32*unit*unit) (256*(p+1))
  have hf := GeneralPaperRayOperandWidthEnvelope.word_add (32*unit*unit+256*(p+1)) 256
  have hp := GeneralPaperInitializerControlCounters.word_le_self p
  have h32 : binaryWordWidth 32=6 := by decide
  have h256 : binaryWordWidth 256=9 := by decide
  have h1 : binaryWordWidth 1=1 := by decide
  unfold magnitude
  omega

theorem input_bounds (unit _p scale : ℕ) (_hUnit : 0<unit) (high low : Number)
    (hHigh : Normal unit high) (hLow : Normal unit low) (hScale : scale≤unit) :
    high.mantissa*scale+low.mantissa≤4*unit*unit ∧
      GeneralPaperDyadicAlignment.divisor unit (high.mantissa*scale+low.mantissa) scale≤2*unit := by
  have hh : high.mantissa≤2*unit := by rcases hHigh with h|h <;> omega
  have hl : low.mantissa≤2*unit := by rcases hLow with h|h <;> omega
  have hm := Nat.mul_le_mul hh hScale
  have hs : unit≤unit*unit := by nlinarith only [_hUnit]
  constructor
  · nlinarith only [hm,hl,hs]
  · unfold GeneralPaperDyadicAlignment.divisor
    split <;> omega

theorem raw_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (unit p : ℕ)
    (hUnit : 0<unit) (hPower : unit=2^p) (high low : Number)
    (hHigh : Normal unit high) (hLow : Normal unit low) (scale scaleWork : ℕ)
    (hScale : scale≤unit) (hWork : scaleWork≤8*p+2) :
    rawCost primitive unit p high low scale scaleWork≤24*primitive (width p high low) := by
  let N := magnitude unit p
  let L := width p high low
  have hNW : 1+binaryWordWidth N≤L := by
    have h := natural_word unit p hPower
    dsimp [N,L,width]
    omega
  have hh : high.mantissa≤2*unit := by rcases hHigh with h|h <;> omega
  have hl : low.mantissa≤2*unit := by rcases hLow with h|h <;> omega
  have hs : unit≤unit*unit := by nlinarith only [hUnit]
  have hProduct : high.mantissa*scale≤2*unit*unit := Nat.mul_le_mul hh hScale
  have hThreshold : 2*unit*scale≤2*unit*unit := Nat.mul_le_mul_left (2*unit) hScale
  have hInput := (input_bounds unit p scale hUnit high low hHigh hLow hScale).1
  have hCore : 4*unit*unit+2*unit+2≤N := by dsimp [N,magnitude]; nlinarith only [hs]
  have hThresholdN : 2*unit*scale≤N := by nlinarith only [hThreshold,hCore]
  have hMeta : 8*p+2+12*(p+1)+66≤N := by dsimp [N,magnitude]; omega
  have hLarge : 256≤N := by dsimp [N,magnitude]; omega
  have price (op : ℕ → ℕ → ℕ) (a b : ℕ) (ha : a≤N) (hb : b≤N) (hc : op a b≤N) :
      GeneralPaperNaturalPrimitivePrice.binary primitive op a b≤2*primitive L :=
    (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono op a b N ha hb hc).trans
      (Nat.mul_le_mul_left 2 (hMono hNW))
  have a := price (fun a b => a*b) high.mantissa scale (by omega) (by omega) (by omega)
  have b := price (fun a b => a+b) (high.mantissa*scale) low.mantissa (by omega) (by omega) (by omega)
  have c := price (fun a b => a*b) 2 unit (by omega) (by omega) (by omega)
  have d := price (fun a b => a*b) (2*unit) scale (by omega) (by omega) (by omega)
  have e := price (fun a b => a*b) 2 scale (by omega) (by omega) (by omega)
  have f := GeneralPaperIntegerWordPrice.compare_le primitive hMono (2*unit*scale) (high.mantissa*scale+low.mantissa) L
    ((Nat.add_le_add_left (binaryWordWidth_mono (by omega : 2*unit*scale≤N)) 1).trans hNW)
    ((Nat.add_le_add_left (binaryWordWidth_mono (by omega : high.mantissa*scale+low.mantissa≤N)) 1).trans hNW)
  have g := price (fun a b => a+b) p 1 (by omega) (by omega) (by omega)
  have h := price (fun a b => a*b) 12 (p+1) (by omega) (by omega) (by omega)
  have i := price (fun a b => a+b) (12*(p+1)) 66 (by omega) (by omega) (by omega)
  have j := price (fun a b => a+b) scaleWork (12*(p+1)+66) (by omega) (by omega) (by omega)
  let bump : ℤ := if 2*unit*scale≤ high.mantissa*scale+low.mantissa then 1 else 0
  have hBump : bump.natAbs≤1 := by dsimp [bump]; split <;> decide
  have hOut : (high.exponent+bump).natAbs≤high.exponent.natAbs+1 := by omega
  have hSum := GeneralPaperRayOperandWidthEnvelope.word_add high.exponent.natAbs 1
  have hOne : binaryWordWidth 1=1 := by decide
  have hBWord := binaryWordWidth_mono hBump
  have hOWord := binaryWordWidth_mono hOut
  have hBW : GeneralPaperIntegerPrimitivePrice.word bump≤L := by
    dsimp [L,width,GeneralPaperIntegerPrimitivePrice.word]; omega
  have hCast := hMono hBW
  have hSigned := GeneralPaperIntegerWordPrice.integer_binary primitive hMono (fun a b => a+b) high.exponent bump L
    (by dsimp [L,width,GeneralPaperIntegerPrimitivePrice.word]; omega) hBW
    (by dsimp [L,width,GeneralPaperIntegerPrimitivePrice.word]; omega)
  change _≤24*primitive L
  unfold rawCost
  change GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) high.mantissa scale+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (high.mantissa*scale) low.mantissa+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 unit+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) (2*unit) scale+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 scale+
    GeneralPaperIntegerWordPrice.compare primitive (2*unit*scale) (high.mantissa*scale+low.mantissa)+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) p 1+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 12 (p+1)+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (12*(p+1)) 66+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) scaleWork (12*(p+1)+66)+
    primitive (GeneralPaperIntegerPrimitivePrice.word bump)+
    GeneralPaperIntegerPrimitivePrice.binary primitive (fun a b => a+b) high.exponent bump≤_
  omega

end Blotto.GeneralPaperRoundedAdditionOperands
