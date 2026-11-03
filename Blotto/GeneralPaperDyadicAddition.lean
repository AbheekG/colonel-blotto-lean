import Blotto.GeneralPaperDyadicAlignment

/-! Stored positive addition with a bounded alignment shift. Farther inputs
are discarded with a proved error allowance; near inputs align at most p
bits, add exact integer mantissas and normalize by a bounded quotient. No
expanded 2^encodedExponent is evaluated.
-/
namespace Blotto.GeneralPaperDyadicAddition
open GeneralPaperDyadicFloat GeneralPaperDyadicAlignment
open GeneralPaperDyadicMultiply (Result)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def ordered (unit p : ℕ) (high low : Number) : Result :=
  let degree := gap high low
  if p<degree then ⟨high,12⟩ else
    let scale := GeneralPaperScoreScaleParameters.powerRun degree
    let input := alignedSum high low scale.power
    let d := divisor unit input scale.power
    let q := GeneralPaperBoundedQuotient.run (input:ℚ) d (p+1)
    ⟨⟨q.quotient,high.exponent+(offset unit input scale.power:ℤ)⟩,scale.work+q.work+64⟩

def add (unit p : ℕ) (left right : Number) : Result :=
  if left.mantissa=0 then ⟨right,8⟩ else
    if right.mantissa=0 then ⟨left,8⟩ else
      let answer := if right.exponent≤left.exponent then ordered unit p left right else ordered unit p right left
      ⟨answer.number,answer.work+16⟩

theorem ordered_normal (unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p)
    (high low : Number) (hHigh : unit≤high.mantissa ∧ high.mantissa<2*unit)
    (hLow : unit≤low.mantissa ∧ low.mantissa<2*unit) : Normal unit (ordered unit p high low).number := by
  unfold ordered
  dsimp only
  split
  · exact Or.inr hHigh
  · dsimp only
    have hScale : 0<(GeneralPaperScoreScaleParameters.powerRun (gap high low)).power := by
      rw [(GeneralPaperScoreScaleParameters.power_data _).1]; positivity
    have hc := alignment_bounds unit _ (by omega) hScale high low hHigh hLow
    exact Or.inr (GeneralPaperMantissaQuotient.normal unit p _ _ (by omega) hPower hc.1 hc.2.1 hc.2.2)

theorem ordered_positive (unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p)
    (high low : Number) (hHigh : unit≤high.mantissa ∧ high.mantissa<2*unit)
    (hLow : unit≤low.mantissa ∧ low.mantissa<2*unit) : 0<(ordered unit p high low).number.mantissa := by
  unfold ordered
  dsimp only
  split
  · dsimp only; omega
  · dsimp only
    have hScale : 0<(GeneralPaperScoreScaleParameters.powerRun (gap high low)).power := by
      rw [(GeneralPaperScoreScaleParameters.power_data _).1]; positivity
    have hc := alignment_bounds unit _ (by omega) hScale high low hHigh hLow
    have hn := GeneralPaperMantissaQuotient.normal unit p _ _ (by omega) hPower hc.1 hc.2.1 hc.2.2
    omega

theorem ordered_certificate (unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p)
    (high low : Number) (hHigh : unit≤high.mantissa ∧ high.mantissa<2*unit)
    (hLow : unit≤low.mantissa ∧ low.mantissa<2*unit) (hOrder : low.exponent≤high.exponent) :
    retention unit*(value high+value low)≤value (ordered unit p high low).number ∧
      value (ordered unit p high low).number≤value high+value low := by
  unfold ordered
  dsimp only
  split
  · rename_i hFar
    exact discard_certificate unit p hUnit hPower high low hHigh hLow hOrder hFar
  · rename_i hNear
    let degree := gap high low
    let scale := (GeneralPaperScoreScaleParameters.powerRun degree).power
    let input := alignedSum high low scale
    let d := divisor unit input scale
    let q := GeneralPaperBoundedQuotient.run (input:ℚ) d (p+1)
    have hScale : scale=2^degree := (GeneralPaperScoreScaleParameters.power_data _).1
    have hScalePos : 0<scale := by rw [hScale]; positivity
    have hc := alignment_bounds unit scale (by omega) hScalePos high low hHigh hLow
    have hRel := GeneralPaperMantissaQuotient.relative unit p input d (by omega) hPower hc.1 hc.2.1 hc.2.2
    have hGap := gap_identity high low hOrder
    have hInput := aligned_value high low degree scale hGap hScale
    have hD : (d:ℚ)=(2:ℚ)^(degree+offset unit input scale) := by
      exact_mod_cast divisor_power unit input scale degree hScale
    have hExp : high.exponent+(offset unit input scale:ℤ)=low.exponent+((degree+offset unit input scale:ℕ):ℤ) := by
      push_cast
      dsimp only [degree] at *
      omega
    have hOut : value ⟨q.quotient,high.exponent+(offset unit input scale:ℤ)⟩=
        ((d:ℚ)*(q.quotient:ℚ))*(2:ℚ)^low.exponent := by
      unfold value
      dsimp only
      rw [hExp,zpow_add₀ (by norm_num),zpow_natCast,← hD]
      ring
    change retention unit*(value high+value low)≤value ⟨q.quotient,high.exponent+(offset unit input scale:ℤ)⟩ ∧
      value ⟨q.quotient,high.exponent+(offset unit input scale:ℤ)⟩≤value high+value low
    rw [hOut,hInput]
    have hScaleReal : (0:ℚ)≤(2:ℚ)^low.exponent := by positivity
    constructor
    · have he := mul_le_mul_of_nonneg_right hRel.1 hScaleReal
      nlinarith only [he]
    · exact mul_le_mul_of_nonneg_right hRel.2 hScaleReal

theorem ordered_work (unit p : ℕ) (high low : Number) :
    (ordered unit p high low).work≤8*p+12*(p+1)+68 := by
  unfold ordered
  dsimp only
  split
  · dsimp only; omega
  · rename_i hNear
    dsimp only
    rw [(GeneralPaperScoreScaleParameters.power_data _).2.2,GeneralPaperBoundedQuotient.run_work]
    omega

theorem add_normal (unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p)
    (left right : Number) (hLeft : Normal unit left) (hRight : Normal unit right) :
    Normal unit (add unit p left right).number := by
  unfold add
  split
  · exact hRight
  · rename_i hL
    split
    · exact hLeft
    · rename_i hR
      have hl := hLeft.resolve_left (by intro h; exact hL h.1)
      have hr := hRight.resolve_left (by intro h; exact hR h.1)
      split
      · exact ordered_normal unit p hUnit hPower left right hl hr
      · exact ordered_normal unit p hUnit hPower right left hr hl

theorem add_certificate (unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p)
    (left right : Number) (hLeft : Normal unit left) (hRight : Normal unit right) :
    retention unit*(value left+value right)≤value (add unit p left right).number ∧
      value (add unit p left right).number≤value left+value right := by
  have hRet := retention_bounds unit hUnit
  unfold add
  split
  · rename_i hZero
    have hz := (value_zero_iff left).mpr hZero
    rw [hz,zero_add]
    exact ⟨mul_le_of_le_one_left (value_nonnegative right) hRet.2,le_refl _⟩
  · rename_i hL
    split
    · rename_i hZero
      have hz := (value_zero_iff right).mpr hZero
      rw [hz,add_zero]
      exact ⟨mul_le_of_le_one_left (value_nonnegative left) hRet.2,le_refl _⟩
    · rename_i hR
      have hl := hLeft.resolve_left (by intro h; exact hL h.1)
      have hr := hRight.resolve_left (by intro h; exact hR h.1)
      split
      · rename_i hOrder
        exact ordered_certificate unit p hUnit hPower left right hl hr hOrder
      · rename_i hOrder
        simpa only [add_comm] using ordered_certificate unit p hUnit hPower right left hr hl (by omega)

theorem add_positive (unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p)
    (left right : Number) (hLeft : Normal unit left) (hRight : Normal unit right)
    (hPositive : 0<left.mantissa ∨ 0<right.mantissa) : 0<(add unit p left right).number.mantissa := by
  unfold add
  split
  · rename_i hZero
    dsimp only
    omega
  · rename_i hL
    split
    · dsimp only; omega
    · rename_i hR
      have hl := hLeft.resolve_left (by intro h; exact hL h.1)
      have hr := hRight.resolve_left (by intro h; exact hR h.1)
      split
      · exact ordered_positive unit p hUnit hPower left right hl hr
      · exact ordered_positive unit p hUnit hPower right left hr hl

theorem add_work (unit p : ℕ) (left right : Number) :
    (add unit p left right).work≤8*p+12*(p+1)+84 := by
  unfold add
  split
  · dsimp only; omega
  · split
    · dsimp only; omega
    · split
      · have h := ordered_work unit p left right
        dsimp only; omega
      · have h := ordered_work unit p right left
        dsimp only; omega

end Blotto.GeneralPaperDyadicAddition
