import Blotto.GeneralPaperRoundedAdditionArithmetic

/-! All costs of the bit implementation are calibrated from the normal
mantissas, precision and encoded exponents. The bounded quotient is replaced
by one division of constructed integers; all its input/output words fit.
-/
namespace Blotto.GeneralPaperRoundedAdditionEnvelope
open GeneralPaperDyadicFloat GeneralPaperDyadicAlignment GeneralPaperRoundedAdditionExecution
open GeneralPaperRoundedAdditionOperands
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem ordered_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W unit p : ℕ)
    (hUnit : 0<unit) (hPower : unit=2^p) (high low : Number) (hHigh : Normal unit high) (hLow : Normal unit low) :
    (orderedWith (GeneralPaperAlignmentPowerPrice.run primitive W) (bitQuotient primitive) primitive W unit p high low).2≤
      2048*(p+1)*(W+primitive (width p high low)) := by
  let L := width p high low
  have hGap := GeneralPaperDyadicComparisonEnvelope.gap_work primitive hMono p high.exponent low.exponent
  change _≤4*primitive L at hGap
  unfold orderedWith
  dsimp only
  split
  · change _≤2048*(p+1)*(W+primitive L)
    nlinarith only [hGap,Nat.zero_le p]
  · rename_i hNear
    let s := GeneralPaperAlignmentPowerPrice.run primitive W (gap high low)
    have hS : s.1.power=2^(gap high low) := by
      dsimp only [s]
      rw [GeneralPaperAlignmentPowerPrice.data,(GeneralPaperScoreScaleParameters.power_data _).1]
    have hSW : s.1.work=8*(gap high low)+2 := by
      dsimp only [s]
      rw [GeneralPaperAlignmentPowerPrice.data,(GeneralPaperScoreScaleParameters.power_data _).2.2]
    have hScale : s.1.power≤unit := by
      rw [hS,hPower]
      exact Nat.pow_le_pow_right (by decide : 0<2) (by omega)
    have hRaw := GeneralPaperRoundedAdditionOperands.raw_work primitive hMono unit p hUnit hPower high low hHigh hLow
      s.1.power s.1.work hScale (by omega)
    have hp := GeneralPaperAlignmentPowerPrice.work primitive hMono W (gap high low)
    have hWord := GeneralPaperInitializerControlCounters.word_le_self (gap high low)
    have hPowerBound : s.2≤512*(p+1)*(W+primitive L) :=
      hp.trans (Nat.mul_le_mul
        (by nlinarith only [hWord,hNear])
        (Nat.add_le_add_left (hMono (by dsimp [L,width]; omega)) W))
    let N := magnitude unit p
    have hNW : 1+binaryWordWidth N≤L := by
      have hh := natural_word unit p hPower
      dsimp [N,L,width]; omega
    have hInput := input_bounds unit p s.1.power hUnit high low hHigh hLow hScale
    have hCore : 4*unit*unit+2*unit≤N := by
      have hh : unit≤unit*unit := by nlinarith only [hUnit]
      dsimp [N,magnitude]
      nlinarith only [hh]
    let input := alignedSum high low s.1.power
    let d := divisor unit input s.1.power
    have hI : input≤N := by dsimp only [input,alignedSum]; omega
    have hD : d≤N := by dsimp only [d,input,alignedSum]; omega
    have hQuot := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a/b) input d N hI hD
      ((Nat.div_le_self input d).trans hI)
    have hQ := hQuot.trans (Nat.mul_le_mul_left 2 (hMono hNW))
    change GeneralPaperDyadicComparisonPrice.gapCost primitive p high.exponent low.exponent+64*W+s.2+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a/b) input d+
      rawCost primitive unit p high low s.1.power s.1.work+128*W≤2048*(p+1)*(W+primitive L)
    change _≤24*primitive L at hRaw
    nlinarith only [hGap,hPowerBound,hQ,hRaw,Nat.zero_le p]

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W unit p : ℕ)
    (hUnit : 0<unit) (hPower : unit=2^p) (left right : Number) (hLeft : Normal unit left) (hRight : Normal unit right) :
    (run primitive W unit p left right).2≤4096*(p+1)*(W+primitive (width p left right)) := by
  let L := width p left right
  let N := magnitude unit p
  have hNW : 1+binaryWordWidth N≤L := by
    have hh := natural_word unit p hPower
    dsimp [N,L,width]; omega
  have hCore : 2*unit≤N := by
    have hh : unit≤unit*unit := by nlinarith only [hUnit]
    dsimp [N,magnitude]; nlinarith only [hh]
  have hL : left.mantissa≤N := by rcases hLeft with h|h <;> omega
  have hR : right.mantissa≤N := by rcases hRight with h|h <;> omega
  have hl := GeneralPaperIntegerWordPrice.compare_le primitive hMono left.mantissa 0 L
    ((Nat.add_le_add_left (binaryWordWidth_mono hL) 1).trans hNW)
    ((Nat.add_le_add_left (binaryWordWidth_mono (Nat.zero_le N)) 1).trans hNW)
  have hr := GeneralPaperIntegerWordPrice.compare_le primitive hMono right.mantissa 0 L
    ((Nat.add_le_add_left (binaryWordWidth_mono hR) 1).trans hNW)
    ((Nat.add_le_add_left (binaryWordWidth_mono (Nat.zero_le N)) 1).trans hNW)
  have he := hMono (show max (GeneralPaperIntegerPrimitivePrice.word left.exponent)
      (GeneralPaperIntegerPrimitivePrice.word right.exponent)≤L by
    dsimp [L,width,GeneralPaperIntegerPrimitivePrice.word]; omega)
  let ordered := orderedWith (GeneralPaperAlignmentPowerPrice.run primitive W) (bitQuotient primitive) primitive W unit p
  have hOrdered (high low : Number) (hh : Normal unit high) (hl : Normal unit low) :
      (ordered high low).2≤2048*(p+1)*(W+primitive (width p high low)) :=
    ordered_work primitive hMono W unit p hUnit hPower high low hh hl
  have hMeta (high low : Number) :
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (ordered high low).1.work 16≤2*primitive L := by
    have hw := GeneralPaperRoundedAdditionArithmetic.ordered_annotation
      (GeneralPaperAlignmentPowerPrice.run primitive W) (GeneralPaperAlignmentPowerPrice.data primitive W)
      (bitQuotient primitive) primitive W unit p high low
    change (ordered high low).1.work≤20*p+80 at hw
    have hN : 20*p+96≤N := by dsimp [N,magnitude]; omega
    exact (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a+b) (ordered high low).1.work 16 N
      (by omega) (by omega) (by omega)).trans (Nat.mul_le_mul_left 2 (hMono hNW))
  have hSymm : width p right left=L := by dsimp [L,width]; omega
  unfold run addWith
  dsimp only
  split
  · change _≤4096*(p+1)*(W+primitive L)
    nlinarith only [hl,Nat.zero_le p]
  · split
    · change _≤4096*(p+1)*(W+primitive L)
      nlinarith only [hl,hr,Nat.zero_le p]
    · split
      · have h := hOrdered left right hLeft hRight
        have hm := hMeta left right
        change (ordered left right).2+GeneralPaperIntegerWordPrice.compare primitive left.mantissa 0+
          GeneralPaperIntegerWordPrice.compare primitive right.mantissa 0+
          primitive (max (GeneralPaperIntegerPrimitivePrice.word left.exponent) (GeneralPaperIntegerPrimitivePrice.word right.exponent))+
          GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (ordered left right).1.work 16+96*W≤
            4096*(p+1)*(W+primitive L)
        change _≤2048*(p+1)*(W+primitive L) at h
        nlinarith only [h,hl,hr,he,hm,Nat.zero_le p]
      · have h := hOrdered right left hRight hLeft
        rw [hSymm] at h
        have hm := hMeta right left
        change (ordered right left).2+GeneralPaperIntegerWordPrice.compare primitive left.mantissa 0+
          GeneralPaperIntegerWordPrice.compare primitive right.mantissa 0+
          primitive (max (GeneralPaperIntegerPrimitivePrice.word left.exponent) (GeneralPaperIntegerPrimitivePrice.word right.exponent))+
          GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (ordered right left).1.work 16+96*W≤
            4096*(p+1)*(W+primitive L)
        nlinarith only [h,hl,hr,he,hm,Nat.zero_le p]

end Blotto.GeneralPaperRoundedAdditionEnvelope
