import Blotto.GeneralPaperActualMeshPairPrice

/-! Integer primal/response and signed loss increments are formed directly
from cached mesh counts. Every raw product, sum and truncated subtraction is
priced; no rational loss expression is evaluated by the implementation.
-/
namespace Blotto.GeneralPaperIncrementPrice
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def cap (mesh : ℕ) : ℕ := 8*mesh+8

def unsignedCost (price : ℕ → ℕ) (factor mesh lo hi pos neg : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) factor mesh+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 pos+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (factor*mesh) (2*pos)+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) lo hi+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 neg+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (lo+hi) (2*neg)+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) (factor*mesh+2*pos) (lo+hi+2*neg)

def unsigned (price : ℕ → ℕ) (W : ℕ) (response : Bool) (mesh lo hi pos neg : ℕ) : ℕ × ℕ :=
  let factor := if response then 4 else 6
  (factor*mesh+2*pos-(lo+hi+2*neg),unsignedCost price factor mesh lo hi pos neg+64*W)

def signed (price : ℕ → ℕ) (W mesh count : ℕ) (positive hit : Bool) : ℕ × ℕ :=
  let h := if hit then mesh else 0
  let base := 4*mesh
  let a := if positive then 2*h else 2*count
  let b := if positive then 2*count else 2*h
  (base+a-b,GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 4 mesh+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 h+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 count+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) base a+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) (base+a) b+64*W)

theorem unsigned_data (price : ℕ → ℕ) (W : ℕ) (response : Bool) (mesh lo hi pos neg : ℕ) :
    (unsigned price W response mesh lo hi pos neg).1=
      if response then GeneralPaperRoundedLosses.responseIncrement mesh lo hi pos neg
      else GeneralPaperRoundedLosses.primalIncrement mesh lo hi pos neg := by cases response <;> rfl

theorem signed_data (price : ℕ → ℕ) (W mesh count : ℕ) (positive hit : Bool) :
    (signed price W mesh count positive hit).1=GeneralPaperRoundedLosses.signedIncrement mesh count positive hit := by
  cases positive <;> rfl

theorem operand_word (m lambda k Qv : ℕ) :
    1+binaryWordWidth (cap (GeneralPaperSourceParameters.prepare k).meshDenominator)≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  let mesh := (GeneralPaperSourceParameters.prepare k).meshDenominator
  have hm := GeneralPaperNatPowerOperands.power_width 2 (29+k)
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2,←(GeneralPaperSourceParameters.data k).2.2.2.2.1] at hm
  change binaryWordWidth mesh≤1+(29+k)*2 at hm
  have h8 := binaryWordWidth_mul 8 mesh
  have hs := GeneralPaperRayOperandWidthEnvelope.word_add (8*mesh) 8
  have hEight : binaryWordWidth 8=4 := by decide
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  change 1+binaryWordWidth (8*mesh+8)≤_
  unfold GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

theorem unsigned_cost_work (price : ℕ → ℕ) (hMono : Monotone price) (factor mesh lo hi pos neg : ℕ)
    (hFactor : factor≤6) (hLo : lo≤mesh) (hHi : hi≤mesh) (hPos : pos≤mesh) (hNeg : neg≤mesh) :
    unsignedCost price factor mesh lo hi pos neg≤14*price (1+binaryWordWidth (cap mesh)) := by
  have hf := Nat.mul_le_mul_right mesh hFactor
  have h1 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a*b) factor mesh (cap mesh)
    (by unfold cap; omega) (by unfold cap; omega) (by unfold cap; omega)
  have h2 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a*b) 2 pos (cap mesh)
    (by unfold cap; omega) (by unfold cap; omega) (by unfold cap; omega)
  have h3 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) (factor*mesh) (2*pos) (cap mesh)
    (by unfold cap; omega) (by unfold cap; omega) (by unfold cap; omega)
  have h4 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) lo hi (cap mesh)
    (by unfold cap; omega) (by unfold cap; omega) (by unfold cap; omega)
  have h5 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a*b) 2 neg (cap mesh)
    (by unfold cap; omega) (by unfold cap; omega) (by unfold cap; omega)
  have h6 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) (lo+hi) (2*neg) (cap mesh)
    (by unfold cap; omega) (by unfold cap; omega) (by unfold cap; omega)
  have h7 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a-b) (factor*mesh+2*pos) (lo+hi+2*neg) (cap mesh)
    (by unfold cap; omega) (by unfold cap; omega) ((Nat.sub_le _ _).trans (by unfold cap; omega))
  unfold unsignedCost
  omega

theorem unsigned_work (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv mesh lo hi pos neg : ℕ)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hLo : lo≤mesh) (hHi : hi≤mesh) (hPos : pos≤mesh) (hNeg : neg≤mesh) (response : Bool) :
    (unsigned price W response mesh lo hi pos neg).2≤
      14*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+64*W := by
  have hf : (if response then 4 else 6:ℕ)≤6 := by split <;> omega
  have h := unsigned_cost_work price hMono _ mesh lo hi pos neg hf hLo hHi hPos hNeg
  have hw : 1+binaryWordWidth (cap mesh)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    rw [hMesh]; exact operand_word m lambda k Qv
  exact Nat.add_le_add_right (h.trans (Nat.mul_le_mul_left 14 (hMono hw))) _

theorem signed_work (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv mesh count : ℕ)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hCount : count≤mesh) (positive hit : Bool) :
    (signed price W mesh count positive hit).2≤
      10*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+64*W := by
  let h := if hit then mesh else 0
  let a := if positive then 2*h else 2*count
  let b := if positive then 2*count else 2*h
  have hh : h≤mesh := by dsimp only [h]; split <;> omega
  have ha : a≤2*mesh := by dsimp only [a]; split <;> omega
  have hb : b≤2*mesh := by dsimp only [b]; split <;> omega
  have h1 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a*b) 4 mesh (cap mesh)
    (by unfold cap; omega) (by unfold cap; omega) (by unfold cap; omega)
  have h2 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a*b) 2 h (cap mesh)
    (by unfold cap; omega) (by unfold cap; omega) (by unfold cap; omega)
  have h3 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a*b) 2 count (cap mesh)
    (by unfold cap; omega) (by unfold cap; omega) (by unfold cap; omega)
  have h4 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) (4*mesh) a (cap mesh)
    (by unfold cap; omega) (by unfold cap; omega) (by unfold cap; omega)
  have h5 := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a-b) (4*mesh+a) b (cap mesh)
    (by unfold cap; omega) (by unfold cap; omega) ((Nat.sub_le _ _).trans (by unfold cap; omega))
  have hw : 1+binaryWordWidth (cap mesh)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    rw [hMesh]; exact operand_word m lambda k Qv
  have hs : (signed price W mesh count positive hit).2≤10*price (1+binaryWordWidth (cap mesh))+64*W := by
    change GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 4 mesh+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 h+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 count+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (4*mesh) a+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) (4*mesh+a) b+64*W≤_
    omega
  exact hs.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 10 (hMono hw)) _)

theorem unsigned_arithmetic (response : Bool) (mesh lo hi pos neg : ℕ) :
    (unsigned (fun _ => 1) 1 response mesh lo hi pos neg).2=78 := rfl

theorem signed_arithmetic (mesh count : ℕ) (positive hit : Bool) :
    (signed (fun _ => 1) 1 mesh count positive hit).2=74 := rfl

end Blotto.GeneralPaperIncrementPrice
