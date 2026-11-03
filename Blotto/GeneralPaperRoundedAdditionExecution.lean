import Blotto.GeneralPaperActualComparisonPrice

/-! One ordered addition shares its bounded alignment power, integer sum,
normalization decision and quotient. Bit and unit arithmetic select distinct
quotient implementations. Every input test, raw operation, native metadata
addition and return write is included in the analytical price.
-/
namespace Blotto.GeneralPaperRoundedAdditionExecution
open GeneralPaperDyadicFloat GeneralPaperDyadicAlignment
open GeneralPaperDyadicMultiply (Result)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def rawCost (primitive : ℕ → ℕ) (unit p : ℕ) (high low : Number) (scale scaleWork : ℕ) : ℕ :=
  let product := high.mantissa*scale
  let input := product+low.mantissa
  let threshold := 2*unit*scale
  let bump : ℤ := if threshold≤ input then 1 else 0
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) high.mantissa scale+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) product low.mantissa+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 unit+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) (2*unit) scale+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 scale+
  GeneralPaperIntegerWordPrice.compare primitive threshold input+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) p 1+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 12 (p+1)+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (12*(p+1)) 66+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) scaleWork (12*(p+1)+66)+
  primitive (GeneralPaperIntegerPrimitivePrice.word bump)+
  GeneralPaperIntegerPrimitivePrice.binary primitive (fun a b => a+b) high.exponent bump

def orderedWith (power : ℕ → GeneralPaperPowerCeiling.Result × ℕ)
    (quotient : ℕ → ℕ → ℕ → ℕ × ℕ) (primitive : ℕ → ℕ) (W unit p : ℕ) (high low : Number) : Result × ℕ :=
  let degree := gap high low
  let common := GeneralPaperDyadicComparisonPrice.gapCost primitive p high.exponent low.exponent+64*W
  if p<degree then (⟨high,12⟩,common) else
    let scale := power degree
    let input := high.mantissa*scale.1.power+low.mantissa
    let large := decide (2*unit*scale.1.power≤ input)
    let d := if large then 2*scale.1.power else scale.1.power
    let bump : ℕ := if large then 1 else 0
    let q := quotient input d (p+1)
    (⟨⟨q.1,high.exponent+(bump:ℤ)⟩,scale.1.work+(12*(p+1)+66)⟩,
      common+scale.2+q.2+rawCost primitive unit p high low scale.1.power scale.1.work+128*W)

def bitQuotient (primitive : ℕ → ℕ) (n d _depth : ℕ) : ℕ × ℕ :=
  (n/d,GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a/b) n d)

def arithmeticQuotient (n d depth : ℕ) : ℕ × ℕ :=
  let q := GeneralPaperBoundedQuotient.run (n:ℚ) d depth
  (q.quotient,q.work+16)

def addWith (ordered : Number → Number → Result × ℕ) (primitive : ℕ → ℕ)
    (W : ℕ) (left right : Number) : Result × ℕ :=
  let leftTest := GeneralPaperIntegerWordPrice.compare primitive left.mantissa 0
  if left.mantissa=0 then (⟨right,8⟩,leftTest+32*W) else
    let rightTest := GeneralPaperIntegerWordPrice.compare primitive right.mantissa 0
    if right.mantissa=0 then (⟨left,8⟩,leftTest+rightTest+32*W) else
      let answer := if right.exponent≤left.exponent then ordered left right else ordered right left
      (⟨answer.1.number,answer.1.work+16⟩,answer.2+leftTest+rightTest+
        primitive (max (GeneralPaperIntegerPrimitivePrice.word left.exponent)
          (GeneralPaperIntegerPrimitivePrice.word right.exponent))+
        GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) answer.1.work 16+96*W)

def run (primitive : ℕ → ℕ) (W unit p : ℕ) (left right : Number) : Result × ℕ :=
  addWith (orderedWith (GeneralPaperAlignmentPowerPrice.run primitive W) (bitQuotient primitive) primitive W unit p)
    primitive W left right

def arithmetic (unit p : ℕ) (left right : Number) : Result × ℕ :=
  addWith (orderedWith GeneralPaperAlignmentPowerPrice.arithmetic arithmeticQuotient (fun _ => 1) 1 unit p)
    (fun _ => 1) 1 left right

theorem ordered_data (power : ℕ → GeneralPaperPowerCeiling.Result × ℕ)
    (hPowerRun : ∀ n, (power n).1=GeneralPaperScoreScaleParameters.powerRun n)
    (quotient : ℕ → ℕ → ℕ → ℕ × ℕ)
    (hQuotient : ∀ n d depth, 0<d → n<d*2^depth →
      (quotient n d depth).1=(GeneralPaperBoundedQuotient.run (n:ℚ) d depth).quotient)
    (primitive : ℕ → ℕ) (W unit p : ℕ) (hUnit : 0<unit) (hPower : unit=2^p)
    (high low : Number) (hHigh : unit≤high.mantissa ∧ high.mantissa<2*unit)
    (hLow : unit≤low.mantissa ∧ low.mantissa<2*unit) :
    (orderedWith power quotient primitive W unit p high low).1=GeneralPaperDyadicAddition.ordered unit p high low := by
  unfold orderedWith GeneralPaperDyadicAddition.ordered
  dsimp only
  split
  · rfl
  · dsimp only
    rw [hPowerRun]
    let s := GeneralPaperScoreScaleParameters.powerRun (gap high low)
    have hs : 0<s.power := by rw [(GeneralPaperScoreScaleParameters.power_data _).1]; positivity
    have hc := alignment_bounds unit s.power hUnit hs high low hHigh hLow
    have hCap : alignedSum high low s.power<divisor unit (alignedSum high low s.power) s.power*2^(p+1) := by
      rw [pow_succ,←hPower]
      nlinarith only [hc.2.2]
    have hq := hQuotient (alignedSum high low s.power)
      (divisor unit (alignedSum high low s.power) s.power) (p+1) hc.1 hCap
    change (⟨⟨(quotient (alignedSum high low s.power) (divisor unit (alignedSum high low s.power) s.power) (p+1)).1,
      high.exponent+(offset unit (alignedSum high low s.power) s.power:ℤ)⟩,s.work+(12*(p+1)+66)⟩ : Result)=_
    rw [hq,GeneralPaperBoundedQuotient.run_work]
    congr 1

theorem add_data (ordered : Number → Number → Result × ℕ) (primitive : ℕ → ℕ)
    (W unit p : ℕ) (left right : Number) (hLeft : Normal unit left) (hRight : Normal unit right)
    (hOrdered : ∀ high low, (unit≤high.mantissa ∧ high.mantissa<2*unit) →
      (unit≤low.mantissa ∧ low.mantissa<2*unit) →
      (ordered high low).1=GeneralPaperDyadicAddition.ordered unit p high low) :
    (addWith ordered primitive W left right).1=GeneralPaperDyadicAddition.add unit p left right := by
  unfold addWith GeneralPaperDyadicAddition.add
  split
  · rfl
  · rename_i hL
    split
    · rfl
    · rename_i hR
      have hl := hLeft.resolve_left (by intro h; exact hL h.1)
      have hr := hRight.resolve_left (by intro h; exact hR h.1)
      split
      · dsimp only
        rw [hOrdered left right hl hr]
      · dsimp only
        rw [hOrdered right left hr hl]

theorem data (primitive : ℕ → ℕ) (W unit p : ℕ) (hUnit : 0<unit) (hPower : unit=2^p)
    (left right : Number) (hLeft : Normal unit left) (hRight : Normal unit right) :
    (run primitive W unit p left right).1=GeneralPaperDyadicAddition.add unit p left right := by
  apply add_data _ primitive W unit p left right hLeft hRight
  intro high low hh hl
  apply ordered_data _ (GeneralPaperAlignmentPowerPrice.data primitive W) _ _ primitive W unit p hUnit hPower high low hh hl
  intro n d depth hd hCap
  exact (GeneralPaperFastConstructedDivision.quotient_data n d depth hd hCap).symm

theorem arithmetic_data (unit p : ℕ) (hUnit : 0<unit) (hPower : unit=2^p)
    (left right : Number) (hLeft : Normal unit left) (hRight : Normal unit right) :
    (arithmetic unit p left right).1=GeneralPaperDyadicAddition.add unit p left right := by
  apply add_data _ (fun _ => 1) 1 unit p left right hLeft hRight
  intro high low hh hl
  apply ordered_data _ GeneralPaperAlignmentPowerPrice.arithmetic_data _ _ (fun _ => 1) 1 unit p hUnit hPower high low hh hl
  intro n d depth hd hCap
  rfl

end Blotto.GeneralPaperRoundedAdditionExecution
