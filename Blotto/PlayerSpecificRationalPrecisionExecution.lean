import Blotto.PlayerSpecificFiniteAccuracy
import Blotto.PlayerSpecificNaturalExecution
import Blotto.PlayerSpecificWidthExecution

/-! The actual scaled precision is computed from two measured word lengths,
one natural difference, one dyadic shift and a single exact comparison.
Every intermediate and the input rational are charged. -/
namespace Blotto.PlayerSpecificRationalPrecisionExecution
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame (C : ℕ) (epsilon : ℚ) (a b wa wb candidate power scaled increased : ℕ) : Trace :=
  copyRow [epsilon]++[.control C,.control epsilon.den,.control b,.control a,
    .control wa,.control wb,.control candidate,.control power,.control scaled,
    .control increased]

def run (C : ℕ) (epsilon : ℚ) : ℕ×ℕ :=
  let model:=RationalCostModel.schoolbook
  let numerator:=PlayerSpecificNaturalExecution.binary model (fun a b=>a*b) C epsilon.den
  let b:=epsilon.num.toNat
  let wa:=PlayerSpecificWidthExecution.run model numerator.1
  let wb:=PlayerSpecificWidthExecution.run model b
  let candidate:=PlayerSpecificNaturalExecution.binary model (fun a b=>a-b) wa.1 wb.1
  let power:=PlayerSpecificNaturalExecution.power model 2 candidate.1
  let scaled:=PlayerSpecificNaturalExecution.binary model (fun a b=>a*b) b power.1
  let increased:=PlayerSpecificNaturalExecution.binary model (fun a b=>a+b) candidate.1 1
  let tested:=GeneralPaperIntegerWordPrice.compare model.rat numerator.1 scaled.1
  (if numerator.1≤scaled.1 then candidate.1 else increased.1,
    numerator.2+wa.2+wb.2+candidate.2+power.2+scaled.2+increased.2+tested+
      price model (frame C epsilon numerator.1 b wa.1 wb.1 candidate.1 power.1
        scaled.1 increased.1))

theorem value (C : ℕ) (epsilon : ℚ) (hC : 0<C) (he : 0<epsilon) :
    (run C epsilon).1=PlayerSpecificRationalPrecision.exponent C epsilon := by
  have hd : 0<epsilon.den := epsilon.den_pos
  have ha : 0<C*epsilon.den := Nat.mul_pos hC hd
  have hb : 0<epsilon.num.toNat :=
    Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr he)
  have heq:=widthRatioPrecision_eq (C*epsilon.den) epsilon.num.toNat ha hb
  simp only [run,PlayerSpecificNaturalExecution.binary_value,
    PlayerSpecificNaturalExecution.power_value,PlayerSpecificWidthExecution.value,
    PlayerSpecificRationalPrecision.exponent]
  rw [←heq]
  simp only [widthRatioPrecision,widthRatioCandidate,Nat.shiftLeft_eq]

end Blotto.PlayerSpecificRationalPrecisionExecution
