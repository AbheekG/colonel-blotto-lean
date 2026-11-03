import Blotto.GeneralPaperNativeSelectedSourcePair

/-! Arithmetic-only native selected-cell computation. Adaptive doubling
constructs the quotient, then the odd position 2t+1 is formed once. Fuel is
the constructed value D+1; no input length query or real floor/divmod is
executed. Bit prices observe actual operands and written results. -/
namespace Blotto.GeneralPaperNativeShiftExecution
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

structure Result where
  cell : ℕ
  odd : ℕ
  work : ℕ

def fixedCost (price : ℕ → ℕ) (D S l t : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 l+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (2*l) 1+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) (2*l+1) D+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 S+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) D 1+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 t+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (2*t) 1

def run (bits : Bool) (model : RationalCostModel) (W D S l : ℕ) : Result × ℕ :=
  let price := if bits then model.rat else fun _ => 1
  let numerator := (2*l+1)*D
  let denominator := 2*S
  let fuel := D+1
  let found := GeneralPaperGrowingQuotientBits.run price W numerator denominator fuel
  let t := found.1.quotient
  (⟨t,2*t+1,found.1.work+32⟩,found.2+fixedCost price D S l t+128*W)

theorem numerator_bound (D S l : ℕ) (hD : 0<D) (hl : l<S) : (2*l+1)*D<(2*S)*D := by
  nlinarith only [hD,hl]

theorem fuel_cap (D S l : ℕ) (hD : 0<D) (hS : 0<S) (hl : l<S) :
    (2*l+1)*D<(2*S)*2^(D+1) := by
  have hn := numerator_bound D S l hD hl
  have hp : D<2^(D+1) := lt_trans (Nat.lt_two_pow_self : D<2^D) (GeneralPaperBoundedQuotient.dyadic_cap D)
  exact hn.trans (Nat.mul_lt_mul_of_pos_left hp (by omega : 0<2*S))

theorem quotient_data (bits : Bool) (model : RationalCostModel) (W D S l : ℕ) (hD : 0<D) (hS : 0<S) (hl : l<S) :
    (run bits model W D S l).1.cell=((2*l+1)*D)/(2*S) := by
  have hc := GeneralPaperConstructedNatDivision.quotient_eq ((2*l+1)*D) (2*S) (D+1) (by omega) (fuel_cap D S l hD hS hl)
  have he := congrArg GeneralPaperGrowingQuotient.Result.quotient
    (GeneralPaperNaturalGrowingQuotient.data ((2*l+1)*D) (2*S) (D+1))
  dsimp only [GeneralPaperNaturalGrowingQuotient.lift] at he
  unfold run
  dsimp only
  rw [GeneralPaperGrowingQuotientBits.data,he]
  exact hc

theorem selected_data (bits : Bool) (model : RationalCostModel) (W D S : ℕ) (hD : 0<D) (hS : 0<S) (l : Fin S) :
    (run bits model W D S l.val).1.cell=(GeneralPaperSelectedShift.selected D S hD hS l).val :=
  quotient_data bits model W D S l.val hD hS l.isLt

theorem cell_bound (bits : Bool) (model : RationalCostModel) (W D S l : ℕ) (hD : 0<D) (hS : 0<S) (hl : l<S) :
    (run bits model W D S l).1.cell<D := by
  rw [quotient_data bits model W D S l hD hS hl]
  apply (Nat.div_lt_iff_lt_mul (by omega : 0<2*S)).mpr
  simpa only [Nat.mul_comm D (2*S)] using numerator_bound D S l hD hl

theorem odd_data (bits : Bool) (model : RationalCostModel) (W D S l : ℕ) :
    (run bits model W D S l).1.odd=2*(run bits model W D S l).1.cell+1 := rfl

theorem models_data (model : RationalCostModel) (W D S l : ℕ) :
    (run true model W D S l).1=(run false model 1 D S l).1 := by
  unfold run
  dsimp only
  rw [GeneralPaperGrowingQuotientBits.data,GeneralPaperGrowingQuotientBits.data]

end Blotto.GeneralPaperNativeShiftExecution
