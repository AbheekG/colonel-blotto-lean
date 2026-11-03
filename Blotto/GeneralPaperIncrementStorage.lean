import Blotto.GeneralPaperSourceGridCallbackStorage

/-! Native unsigned/signed increment arithmetic counts every unreduced
integer operand, intermediate and result, branch bits and primitive scratch.
The retained source mesh derives all short counter words, including zero. -/
namespace Blotto.GeneralPaperIncrementStorage
open GeneralPaperEncodedScalarStorage GeneralPaperIncrementPrice
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem source_fields (W m lambda k Qv mesh : ℕ)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (xs : List ℕ) (hx : ∀ x∈xs,x≤cap mesh) :
    fields W xs≤xs.length*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+32*W := by
  apply fields_bound
  intro x hmem
  have hw : natBits (cap mesh)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    rw [hm]
    exact operand_word m lambda k Qv
  exact (Nat.add_le_add_left (binaryWordWidth_mono (hx x hmem)) 1).trans hw

def unsignedWindow (model : RationalCostModel) (W : ℕ) (response : Bool) (mesh lo hi pos neg : ℕ) : ℕ :=
  let factor := if response then 4 else 6
  fields W [mesh,lo,hi,pos,neg,factor,2,factor*mesh,2*pos,factor*mesh+2*pos,lo+hi,2*neg,lo+hi+2*neg,
    (unsigned model.rat W response mesh lo hi pos neg).1]+2+64*W+
    (unsigned model.rat W response mesh lo hi pos neg).2+256*W

def unsignedProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  14*(H+W)+32*W+2+64*W+14*model.rat H+64*W+256*W

theorem unsigned_bounded (model : RationalCostModel) (W m lambda k Qv mesh lo hi pos neg : ℕ) (response : Bool)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hl : lo≤mesh) (hh : hi≤mesh) (hp : pos≤mesh) (hn : neg≤mesh) :
    unsignedWindow model W response mesh lo hi pos neg≤unsignedProfile model W m lambda k Qv := by
  let factor : ℕ := if response then 4 else 6
  have hf : factor≤6 := by dsimp only [factor]; split <;> omega
  have hfm := Nat.mul_le_mul_right mesh hf
  have hs := source_fields W m lambda k Qv mesh hm
    [mesh,lo,hi,pos,neg,factor,2,factor*mesh,2*pos,factor*mesh+2*pos,lo+hi,2*neg,lo+hi+2*neg,
      factor*mesh+2*pos-(lo+hi+2*neg)] (by
        intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals (unfold cap; omega))
  have hprice := unsigned_work model.rat model.monotone W m lambda k Qv mesh lo hi pos neg hm hl hh hp hn response
  change fields W [mesh,lo,hi,pos,neg,factor,2,factor*mesh,2*pos,factor*mesh+2*pos,lo+hi,2*neg,lo+hi+2*neg,
    (unsigned model.rat W response mesh lo hi pos neg).1]≤14*(_+W)+32*W at hs
  dsimp only [unsignedWindow,unsignedProfile]
  dsimp only [factor] at hs
  omega

def signedWindow (model : RationalCostModel) (W mesh count : ℕ) (positive hit : Bool) : ℕ :=
  let h := if hit then mesh else 0
  let a := if positive then 2*h else 2*count
  let b := if positive then 2*count else 2*h
  fields W [mesh,count,h,4,2,4*mesh,2*h,2*count,a,b,4*mesh+a,(signed model.rat W mesh count positive hit).1]+
    4+64*W+(signed model.rat W mesh count positive hit).2+256*W

def signedProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  12*(H+W)+32*W+4+64*W+10*model.rat H+64*W+256*W

theorem signed_bounded (model : RationalCostModel) (W m lambda k Qv mesh count : ℕ) (positive hit : Bool)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hc : count≤mesh) :
    signedWindow model W mesh count positive hit≤signedProfile model W m lambda k Qv := by
  let h := if hit then mesh else 0
  let a := if positive then 2*h else 2*count
  let b := if positive then 2*count else 2*h
  have hh : h≤mesh := by dsimp only [h]; split <;> omega
  have ha : a≤2*mesh := by dsimp only [a]; split <;> omega
  have hb : b≤2*mesh := by dsimp only [b]; split <;> omega
  have hs := source_fields W m lambda k Qv mesh hm [mesh,count,h,4,2,4*mesh,2*h,2*count,a,b,4*mesh+a,4*mesh+a-b] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals (unfold cap; omega))
  have hprice := signed_work model.rat model.monotone W m lambda k Qv mesh count hm hc positive hit
  change fields W [mesh,count,h,4,2,4*mesh,2*h,2*count,a,b,4*mesh+a,(signed model.rat W mesh count positive hit).1]≤12*(_+W)+32*W at hs
  dsimp only [signedWindow,signedProfile]
  dsimp only [h,a,b] at hs
  omega

end Blotto.GeneralPaperIncrementStorage
