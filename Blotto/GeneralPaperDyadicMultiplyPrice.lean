import Blotto.GeneralPaperDyadicFastMultiply

/-! Actual operand prices for fast constructed-mantissa multiplication.
All raw products, tests, division, exponent casts/additions and native work
metadata arithmetic are charged. Encoded exponent sizes enter explicitly.
-/
namespace Blotto.GeneralPaperDyadicMultiplyPrice
open GeneralPaperDyadicFloat GeneralPaperDyadicMultiply
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def width (unit p : ℕ) (left right : Number) : ℕ :=
  64+8*(binaryWordWidth unit+binaryWordWidth p+
    binaryWordWidth left.exponent.natAbs+binaryWordWidth right.exponent.natAbs)

def naturalMagnitude (unit p : ℕ) : ℕ := 4*unit*unit+2*unit+p+2
def exponentMagnitude (p : ℕ) (left right : Number) : ℕ := left.exponent.natAbs+right.exponent.natAbs+p+2

theorem natural_word (unit p : ℕ) (left right : Number) :
    1+binaryWordWidth (naturalMagnitude unit p)≤width unit p left right := by
  have h4 := binaryWordWidth_mul 4 unit
  have hs := binaryWordWidth_mul (4*unit) unit
  have hd := binaryWordWidth_mul 2 unit
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (4*unit*unit) (2*unit)
  have hb := GeneralPaperRayOperandWidthEnvelope.word_add (4*unit*unit+2*unit) p
  have hc := GeneralPaperRayOperandWidthEnvelope.word_add (4*unit*unit+2*unit+p) 2
  have h2 : binaryWordWidth 2=2 := by decide
  have hFour : binaryWordWidth 4=3 := by decide
  unfold naturalMagnitude width
  omega

theorem exponent_word (unit p : ℕ) (left right : Number) :
    1+binaryWordWidth (exponentMagnitude p left right)≤width unit p left right := by
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add left.exponent.natAbs right.exponent.natAbs
  have hb := GeneralPaperRayOperandWidthEnvelope.word_add (left.exponent.natAbs+right.exponent.natAbs) p
  have hc := GeneralPaperRayOperandWidthEnvelope.word_add (left.exponent.natAbs+right.exponent.natAbs+p) 2
  have h2 : binaryWordWidth 2=2 := by decide
  unfold exponentMagnitude width
  omega

def naturalCost (primitive : ℕ → ℕ) (unit p : ℕ) (left right : Number) : ℕ :=
  let product := left.mantissa*right.mantissa
  let d := divisor unit product
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) left.mantissa right.mantissa+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 unit+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) (2*unit) unit+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a/b) product d+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) p 1+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 12 (p+1)+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (12*(p+1)) 66+
  GeneralPaperIntegerWordPrice.compare primitive (2*unit*unit) product+
  primitive (1+binaryWordWidth d)

theorem natural_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (unit p : ℕ)
    (left right : Number) (hl : Normal unit left) (hr : Normal unit right) :
    naturalCost primitive unit p left right≤16*primitive (width unit p left right) := by
  let L := width unit p left right
  let N := naturalMagnitude unit p
  have hlm : left.mantissa≤2*unit := by rcases hl with h|h <;> omega
  have hrm : right.mantissa≤2*unit := by rcases hr with h|h <;> omega
  have hProd : left.mantissa*right.mantissa≤4*unit*unit := by
    have hh:=Nat.mul_le_mul hlm hrm
    nlinarith only [hh]
  have hDiv : divisor unit (left.mantissa*right.mantissa)≤2*unit := by unfold divisor; split <;> omega
  have hQ := Nat.div_le_self (left.mantissa*right.mantissa) (divisor unit (left.mantissa*right.mantissa))
  have hNW := natural_word unit p left right
  change 1+binaryWordWidth N≤L at hNW
  have a := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a*b) left.mantissa right.mantissa N
    (by dsimp [N,naturalMagnitude]; omega) (by dsimp [N,naturalMagnitude]; omega) (by dsimp [N,naturalMagnitude]; omega)
  have b := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a*b) 2 unit N
    (by dsimp [N,naturalMagnitude]; omega) (by dsimp [N,naturalMagnitude]; omega) (by dsimp [N,naturalMagnitude]; omega)
  have c := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a*b) (2*unit) unit N
    (by dsimp [N,naturalMagnitude]; omega) (by dsimp [N,naturalMagnitude]; omega) (by dsimp [N,naturalMagnitude]; nlinarith)
  have d := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a/b)
    (left.mantissa*right.mantissa) (divisor unit (left.mantissa*right.mantissa)) N
    (by dsimp [N,naturalMagnitude]; omega) (by dsimp [N,naturalMagnitude]; omega) (by dsimp [N,naturalMagnitude]; omega)
  have hPrice := hMono hNW
  have ha := a.trans (Nat.mul_le_mul_left 2 hPrice)
  have hb := b.trans (Nat.mul_le_mul_left 2 hPrice)
  have hc := c.trans (Nat.mul_le_mul_left 2 hPrice)
  have hd := d.trans (Nat.mul_le_mul_left 2 hPrice)
  have hp := GeneralPaperRayOperandWidthEnvelope.word_add p 1
  have h12 := binaryWordWidth_mul 12 (p+1)
  have h66 := GeneralPaperRayOperandWidthEnvelope.word_add (12*(p+1)) 66
  have hOne : binaryWordWidth 1=1 := by decide
  have hTwelve : binaryWordWidth 12=4 := by decide
  have hSixtySix : binaryWordWidth 66=7 := by decide
  have he := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) p 1 L
    (by dsimp [L,width]; omega) (by dsimp [L,width]; omega) (by dsimp [L,width]; omega)
  have hf := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 12 (p+1) L
    (by dsimp [L,width]; omega) (by dsimp [L,width]; omega) (by dsimp [L,width]; omega)
  have hg := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) (12*(p+1)) 66 L
    (by dsimp [L,width]; omega) (by dsimp [L,width]; omega) (by dsimp [L,width]; omega)
  have ht := GeneralPaperIntegerWordPrice.compare_le primitive hMono (2*unit*unit) (left.mantissa*right.mantissa) L
    ((Nat.add_le_add_left (binaryWordWidth_mono (by dsimp [N,naturalMagnitude]; nlinarith : 2*unit*unit≤N)) 1).trans hNW)
    ((Nat.add_le_add_left (binaryWordWidth_mono (by dsimp [N,naturalMagnitude]; omega : left.mantissa*right.mantissa≤N)) 1).trans hNW)
  have hw := hMono ((Nat.add_le_add_left (binaryWordWidth_mono (by dsimp [N,naturalMagnitude]; omega : divisor unit (left.mantissa*right.mantissa)≤N)) 1).trans hNW)
  change _≤16*primitive L
  unfold naturalCost
  dsimp only
  change _≤2*primitive L at ha hb hc hd
  omega

def exponentCost (primitive : ℕ → ℕ) (unit p : ℕ) (left right : Number) : ℕ :=
  let shifted : ℤ := shift unit (left.mantissa*right.mantissa) p
  primitive (GeneralPaperIntegerPrimitivePrice.word shifted)+
  GeneralPaperIntegerPrimitivePrice.binary primitive (fun a b => a+b) left.exponent right.exponent+
  GeneralPaperIntegerPrimitivePrice.binary primitive (fun a b => a+b) (left.exponent+right.exponent) shifted

theorem exponent_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (unit p : ℕ) (left right : Number) :
    exponentCost primitive unit p left right≤5*primitive (width unit p left right) := by
  let R := exponentMagnitude p left right
  let shifted : ℤ := shift unit (left.mantissa*right.mantissa) p
  have hs : shift unit (left.mantissa*right.mantissa) p≤p+1 := by unfold shift; split <;> omega
  have hShift : shifted.natAbs≤p+1 := by simpa only [shifted,Int.natAbs_natCast] using hs
  have hA := Int.natAbs_add_le left.exponent right.exponent
  have hB := Int.natAbs_add_le (left.exponent+right.exponent) shifted
  have ha := GeneralPaperIntegerPrimitivePrice.binary_le primitive hMono (fun a b => a+b) left.exponent right.exponent R
    (by dsimp [R,exponentMagnitude]; omega) (by dsimp [R,exponentMagnitude]; omega) (by dsimp [R,exponentMagnitude]; omega)
  have hb := GeneralPaperIntegerPrimitivePrice.binary_le primitive hMono (fun a b => a+b) (left.exponent+right.exponent) shifted R
    (by dsimp [R,exponentMagnitude]; omega) (by dsimp [R,exponentMagnitude]; omega) (by dsimp [R,exponentMagnitude]; omega)
  have hWord := exponent_word unit p left right
  change 1+binaryWordWidth R≤width unit p left right at hWord
  have hP := hMono hWord
  have hc := hMono ((GeneralPaperIntegerPrimitivePrice.word_bound shifted R (by dsimp [R,exponentMagnitude]; omega)).trans hWord)
  have h1 := ha.trans (Nat.mul_le_mul_left 2 hP)
  have h2 := hb.trans (Nat.mul_le_mul_left 2 hP)
  unfold exponentCost
  change _≤5*primitive (width unit p left right)
  change primitive (GeneralPaperIntegerPrimitivePrice.word shifted)+
    GeneralPaperIntegerPrimitivePrice.binary primitive (fun a b => a+b) left.exponent right.exponent+
    GeneralPaperIntegerPrimitivePrice.binary primitive (fun a b => a+b) (left.exponent+right.exponent) shifted≤
      5*primitive (width unit p left right)
  omega

def cost (primitive : ℕ → ℕ) (W unit p : ℕ) (left right : Number) : ℕ :=
  GeneralPaperIntegerWordPrice.compare primitive left.mantissa 0+
  GeneralPaperIntegerWordPrice.compare primitive right.mantissa 0+
  if left.mantissa=0 ∨ right.mantissa=0 then 32*W
  else naturalCost primitive unit p left right+exponentCost primitive unit p left right+128*W

def run (primitive : ℕ → ℕ) (W unit p : ℕ) (left right : Number) : GeneralPaperDyadicMultiply.Result × ℕ :=
  (GeneralPaperDyadicFastMultiply.run unit p left right,cost primitive W unit p left right)

theorem data (primitive : ℕ → ℕ) (W unit p : ℕ) (hUnit : 0<unit) (hPower : unit=2^p) (left right : Number)
    (hl : Normal unit left) (hr : Normal unit right) :
    (run primitive W unit p left right).1=multiply unit p left right :=
  GeneralPaperDyadicFastMultiply.data unit p hUnit hPower left right hl hr

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W unit p : ℕ) (left right : Number)
    (hl : Normal unit left) (hr : Normal unit right) :
    (run primitive W unit p left right).2≤256*(W+primitive (width unit p left right)) := by
  have hn := natural_work primitive hMono unit p left right hl hr
  have he := exponent_work primitive hMono unit p left right
  have hNW := natural_word unit p left right
  have hlm : left.mantissa≤naturalMagnitude unit p := by rcases hl with h|h <;> dsimp [naturalMagnitude] <;> omega
  have hrm : right.mantissa≤naturalMagnitude unit p := by rcases hr with h|h <;> dsimp [naturalMagnitude] <;> omega
  have hL := GeneralPaperIntegerWordPrice.compare_le primitive hMono left.mantissa 0 (width unit p left right)
    ((Nat.add_le_add_left (binaryWordWidth_mono hlm) 1).trans hNW)
    ((Nat.add_le_add_left (binaryWordWidth_mono (Nat.zero_le (naturalMagnitude unit p))) 1).trans hNW)
  have hR := GeneralPaperIntegerWordPrice.compare_le primitive hMono right.mantissa 0 (width unit p left right)
    ((Nat.add_le_add_left (binaryWordWidth_mono hrm) 1).trans hNW)
    ((Nat.add_le_add_left (binaryWordWidth_mono (Nat.zero_le (naturalMagnitude unit p))) 1).trans hNW)
  change cost primitive W unit p left right≤_
  unfold cost
  split <;> omega

end Blotto.GeneralPaperDyadicMultiplyPrice
