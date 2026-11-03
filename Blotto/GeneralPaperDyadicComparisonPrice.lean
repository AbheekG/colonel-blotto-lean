import Blotto.GeneralPaperAlignmentPowerPrice
import Blotto.GeneralPaperDyadicCompare

/-! Literal comparison prices. Only the near branch constructs a shift.
Zero tests, signed exponent comparison/subtraction, conversion to a natural
gap, the gap test, shifted product, final comparison and metadata are priced.
The power runner selects the bit or the separate unit arithmetic execution.
-/
namespace Blotto.GeneralPaperDyadicComparisonPrice
open GeneralPaperDyadicFloat
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def aligned (power : ℕ → GeneralPaperPowerCeiling.Result × ℕ)
    (primitive : ℕ → ℕ) (W degree a b : ℕ) (reverse : Bool) : GeneralPaperDyadicCompare.Result × ℕ :=
  let shift := power degree
  let product := a*shift.1.power
  let answer := if reverse then decide (product≤b) else decide (b≤product)
  (⟨answer,shift.1.work+24⟩,shift.2+64*W+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) a shift.1.power+
    GeneralPaperIntegerWordPrice.compare primitive product b+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) shift.1.work 24)

def gapCost (primitive : ℕ → ℕ) (width : ℕ) (high low : ℤ) : ℕ :=
  GeneralPaperIntegerPrimitivePrice.binary primitive (fun a b => a-b) high low+
  primitive (1+binaryWordWidth (high-low).toNat)+
  GeneralPaperIntegerWordPrice.compare primitive width (high-low).toNat

def leWith (power : ℕ → GeneralPaperPowerCeiling.Result × ℕ)
    (primitive : ℕ → ℕ) (W width : ℕ) (left right : Number) : GeneralPaperDyadicCompare.Result × ℕ :=
  let leftTest := GeneralPaperIntegerWordPrice.compare primitive left.mantissa 0
  if left.mantissa=0 then (⟨true,8⟩,leftTest+32*W) else
    let rightTest := GeneralPaperIntegerWordPrice.compare primitive right.mantissa 0
    if right.mantissa=0 then (⟨false,8⟩,leftTest+rightTest+32*W) else
      let tests := leftTest+rightTest+
        primitive (max (GeneralPaperIntegerPrimitivePrice.word left.exponent)
          (GeneralPaperIntegerPrimitivePrice.word right.exponent))
      if left.exponent≤right.exponent then
        let gap := (right.exponent-left.exponent).toNat
        let common := tests+gapCost primitive width right.exponent left.exponent+64*W
        if width≤gap then (⟨true,16⟩,common) else
          let result := aligned power primitive W gap right.mantissa left.mantissa false
          (result.1,common+result.2)
      else
        let gap := (left.exponent-right.exponent).toNat
        let common := tests+gapCost primitive width left.exponent right.exponent+64*W
        if width≤gap then (⟨false,16⟩,common) else
          let result := aligned power primitive W gap left.mantissa right.mantissa true
          (result.1,common+result.2)

def run (primitive : ℕ → ℕ) (W width : ℕ) (left right : Number) : GeneralPaperDyadicCompare.Result × ℕ :=
  leWith (GeneralPaperAlignmentPowerPrice.run primitive W) primitive W width left right

def arithmetic (width : ℕ) (left right : Number) : GeneralPaperDyadicCompare.Result × ℕ :=
  leWith GeneralPaperAlignmentPowerPrice.arithmetic (fun _ => 1) 1 width left right

theorem dataWith (power : ℕ → GeneralPaperPowerCeiling.Result × ℕ)
    (hPower : ∀ n, (power n).1=GeneralPaperScoreScaleParameters.powerRun n)
    (primitive : ℕ → ℕ) (W width : ℕ) (left right : Number) :
    (leWith power primitive W width left right).1=GeneralPaperDyadicCompare.le width left right := by
  unfold leWith GeneralPaperDyadicCompare.le
  split
  · rfl
  · split
    · rfl
    · split <;> dsimp only <;> split
      · rfl
      · simp only [aligned,hPower,Bool.false_eq_true,ite_false]
      · rfl
      · simp only [aligned,hPower,ite_true]

theorem data (primitive : ℕ → ℕ) (W width : ℕ) (left right : Number) :
    (run primitive W width left right).1=GeneralPaperDyadicCompare.le width left right :=
  dataWith _ (GeneralPaperAlignmentPowerPrice.data primitive W) _ _ _ _ _

theorem arithmetic_data (width : ℕ) (left right : Number) :
    (arithmetic width left right).1=GeneralPaperDyadicCompare.le width left right :=
  dataWith _ GeneralPaperAlignmentPowerPrice.arithmetic_data _ _ _ _ _

theorem arithmetic_aligned_work (degree a b : ℕ) (reverse : Bool) :
    (aligned GeneralPaperAlignmentPowerPrice.arithmetic (fun _ => 1) 1 degree a b reverse).2≤128*(degree+1)+69 := by
  have h := GeneralPaperAlignmentPowerPrice.arithmetic_work degree
  change (GeneralPaperAlignmentPowerPrice.arithmetic degree).2+64+
    (1+1)+1+(1+1)≤_
  omega

theorem arithmetic_work (width : ℕ) (left right : Number) :
    (arithmetic width left right).2≤512*(width+1) := by
  unfold arithmetic leWith
  dsimp only [GeneralPaperIntegerWordPrice.compare,GeneralPaperNaturalPrimitivePrice.binary,
    GeneralPaperIntegerPrimitivePrice.binary,gapCost]
  split
  · dsimp only; omega
  · split
    · dsimp only; omega
    · split <;> split
      · dsimp only; omega
      · rename_i hNear
        have h := arithmetic_aligned_work (right.exponent-left.exponent).toNat right.mantissa left.mantissa false
        change 1+1+1+(1+1+1+1)+64+_≤_
        omega
      · dsimp only; omega
      · rename_i hNear
        have h := arithmetic_aligned_work (left.exponent-right.exponent).toNat left.mantissa right.mantissa true
        change 1+1+1+(1+1+1+1)+64+_≤_
        omega

end Blotto.GeneralPaperDyadicComparisonPrice
