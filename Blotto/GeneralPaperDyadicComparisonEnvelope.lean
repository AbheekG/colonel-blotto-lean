import Blotto.GeneralPaperDyadicComparisonPrice

/-! Encoded operand bounds for the executed comparison, including its
unrounded shifted product and its signed exponent difference. The word
envelope is analytical; comparison never expands an encoded exponent.
-/
namespace Blotto.GeneralPaperDyadicComparisonEnvelope
open GeneralPaperDyadicFloat GeneralPaperDyadicComparisonPrice
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def width (digits : ℕ) (left right : Number) : ℕ :=
  256+16*(digits+binaryWordWidth left.exponent.natAbs+binaryWordWidth right.exponent.natAbs)

theorem mantissa_word (digits a : ℕ) (ha : a<2^digits) : binaryWordWidth a≤1+2*digits := by
  have h := (binaryWordWidth_mono ha.le).trans (GeneralPaperNatPowerOperands.power_width 2 digits)
  simpa only [show binaryWordWidth 2=2 by decide,Nat.mul_comm] using h

theorem aligned_work (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W digits degree a b : ℕ) (reverse : Bool) (hDegree : degree<digits)
    (ha : a<2^digits) (hb : b<2^digits) :
    (aligned (GeneralPaperAlignmentPowerPrice.run primitive W) primitive W degree a b reverse).2≤
      512*(binaryWordWidth degree+1)*(W+primitive (128+8*digits)) := by
  let L := 128+8*digits
  have hA := mantissa_word digits a ha
  have hB := mantissa_word digits b hb
  have hS : binaryWordWidth (2^degree)≤1+2*degree := by
    simpa only [show binaryWordWidth 2=2 by decide,Nat.mul_comm] using GeneralPaperNatPowerOperands.power_width 2 degree
  have hProd := binaryWordWidth_mul a (2^degree)
  have hDegreeWord := GeneralPaperInitializerControlCounters.word_le_self degree
  have hWorkMul := binaryWordWidth_mul 8 degree
  have hWorkAdd := GeneralPaperRayOperandWidthEnvelope.word_add (8*degree) 2
  have hWorkRet := GeneralPaperRayOperandWidthEnvelope.word_add (8*degree+2) 24
  have h8 : binaryWordWidth 8=4 := by decide
  have h2 : binaryWordWidth 2=2 := by decide
  have h24 : binaryWordWidth 24=5 := by decide
  have hm := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) a (2^degree) L
    (by dsimp [L]; omega) (by dsimp [L]; omega) (by dsimp [L]; omega)
  have hc := GeneralPaperIntegerWordPrice.compare_le primitive hMono (a*2^degree) b L
    (by dsimp [L]; omega) (by dsimp [L]; omega)
  have hw := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) (8*degree+2) 24 L
    (by dsimp [L]; omega) (by dsimp [L]; omega) (by dsimp [L]; omega)
  have hp := (GeneralPaperAlignmentPowerPrice.work primitive hMono W degree).trans
    (Nat.mul_le_mul_left (256*(binaryWordWidth degree+1))
      (Nat.add_le_add_left (hMono (show 32+4*degree≤L by dsimp [L]; omega)) W))
  simp only [aligned,GeneralPaperAlignmentPowerPrice.data,
    (GeneralPaperScoreScaleParameters.power_data degree).1,
    (GeneralPaperScoreScaleParameters.power_data degree).2.2]
  change _≤512*(binaryWordWidth degree+1)*(W+primitive L)
  nlinarith only [hp,hm,hc,hw,Nat.zero_le (binaryWordWidth degree)]

theorem gap_work (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (digits : ℕ) (high low : ℤ) :
    gapCost primitive digits high low≤
      4*primitive (256+16*(digits+binaryWordWidth high.natAbs+binaryWordWidth low.natAbs)) := by
  let L := 256+16*(digits+binaryWordWidth high.natAbs+binaryWordWidth low.natAbs)
  have hDiff : (high-low).natAbs≤high.natAbs+low.natAbs := by omega
  have hNat : (high-low).toNat≤high.natAbs+low.natAbs := by omega
  have hSum := GeneralPaperRayOperandWidthEnvelope.word_add high.natAbs low.natAbs
  have hD := binaryWordWidth_mono hDiff
  have hN := binaryWordWidth_mono hNat
  have hDigits := GeneralPaperInitializerControlCounters.word_le_self digits
  have hd := GeneralPaperIntegerWordPrice.integer_binary primitive hMono (fun a b => a-b) high low L
    (by dsimp [L,GeneralPaperIntegerPrimitivePrice.word]; omega)
    (by dsimp [L,GeneralPaperIntegerPrimitivePrice.word]; omega)
    (by dsimp [L,GeneralPaperIntegerPrimitivePrice.word]; omega)
  have hn := hMono (show 1+binaryWordWidth (high-low).toNat≤L by dsimp [L]; omega)
  have hc := GeneralPaperIntegerWordPrice.compare_le primitive hMono digits (high-low).toNat L
    (by dsimp [L]; omega) (by dsimp [L]; omega)
  change _≤4*primitive L
  unfold gapCost
  omega

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W digits : ℕ) (left right : Number)
    (hLeft : left.mantissa<2^digits) (hRight : right.mantissa<2^digits) :
    (run primitive W digits left right).2≤2048*(digits+1)*(W+primitive (width digits left right)) := by
  let L := width digits left right
  have hA := mantissa_word digits left.mantissa hLeft
  have hB := mantissa_word digits right.mantissa hRight
  have hZero : binaryWordWidth 0=1 := by decide
  have hl := GeneralPaperIntegerWordPrice.compare_le primitive hMono left.mantissa 0 L
    (by dsimp [L,width]; omega) (by dsimp [L,width]; omega)
  have hr := GeneralPaperIntegerWordPrice.compare_le primitive hMono right.mantissa 0 L
    (by dsimp [L,width]; omega) (by dsimp [L,width]; omega)
  have he := hMono (show max (GeneralPaperIntegerPrimitivePrice.word left.exponent)
      (GeneralPaperIntegerPrimitivePrice.word right.exponent)≤L by
    dsimp [L,width,GeneralPaperIntegerPrimitivePrice.word]
    omega)
  have hgl := gap_work primitive hMono digits left.exponent right.exponent
  have hgr := gap_work primitive hMono digits right.exponent left.exponent
  have hEq : 256+16*(digits+binaryWordWidth right.exponent.natAbs+binaryWordWidth left.exponent.natAbs)=L := by
    dsimp [L,width]; omega
  rw [hEq] at hgr
  change _≤4*primitive L at hgl
  have hAligned (d a b : ℕ) (reverse : Bool) (hd : d<digits) (ha : a<2^digits) (hb : b<2^digits) :
      (aligned (GeneralPaperAlignmentPowerPrice.run primitive W) primitive W d a b reverse).2≤
        512*(digits+1)*(W+primitive L) := by
    have h := aligned_work primitive hMono W digits d a b reverse hd ha hb
    have hdWord := GeneralPaperInitializerControlCounters.word_le_self d
    exact h.trans (Nat.mul_le_mul
      (Nat.mul_le_mul_left 512 (by omega))
      (Nat.add_le_add_left (hMono (by dsimp [L,width]; omega)) W))
  unfold run leWith
  dsimp only
  split
  · change _≤2048*(digits+1)*(W+primitive L)
    nlinarith only [hl,Nat.zero_le digits]
  · split
    · change _≤2048*(digits+1)*(W+primitive L)
      nlinarith only [hl,hr,Nat.zero_le digits]
    · split <;> split
      · change _≤2048*(digits+1)*(W+primitive L)
        nlinarith only [hl,hr,he,hgr,Nat.zero_le digits]
      · rename_i hNear
        have h := hAligned (right.exponent-left.exponent).toNat right.mantissa left.mantissa false (by omega) hRight hLeft
        change _≤2048*(digits+1)*(W+primitive L)
        nlinarith only [hl,hr,he,hgr,h,Nat.zero_le digits]
      · change _≤2048*(digits+1)*(W+primitive L)
        nlinarith only [hl,hr,he,hgl,Nat.zero_le digits]
      · rename_i hNear
        have h := hAligned (left.exponent-right.exponent).toNat left.mantissa right.mantissa true (by omega) hLeft hRight
        change _≤2048*(digits+1)*(W+primitive L)
        nlinarith only [hl,hr,he,hgl,h,Nat.zero_le digits]

end Blotto.GeneralPaperDyadicComparisonEnvelope
