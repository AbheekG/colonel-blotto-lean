import Blotto.GeneralPaperCFError

/-! Denominators in the forward reference do not decrease after the first
midpoint term. These facts make rejection of a denominator above D exclude
all later bounded-denominator convergents. Only the proof observer uses
primitive Nat quotient/modulus; the source loop is joined through advance_view.
-/
namespace Blotto.GeneralPaperCFModelOrder
open GeneralPaperCFModel
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem step_order (s : Core) (hOrder : s.denominator≤s.numerator) : (step s).denominator≤(step s).numerator := by
  by_cases hz : s.denominator=0
  · simpa only [step,ite_eq_left hz] using hOrder
  · simp only [step,ite_eq_right hz]
    exact (Nat.mod_lt s.numerator (by omega)).le

theorem step_den_mono (s : Core) (hOrder : s.denominator≤s.numerator) : s.previousDen≤(step s).previousDen := by
  by_cases hz : s.denominator=0
  · simp only [step,ite_eq_left hz,le_refl]
  · have hd : 0<s.denominator := by omega
    have hq : 1≤s.numerator/s.denominator :=
      (Nat.le_div_iff_mul_le hd).mpr (by simpa only [Nat.one_mul] using hOrder)
    have he := Nat.mul_le_mul_right s.previousDen hq
    simp only [step,ite_eq_right hz]
    nlinarith only [he]

theorem iterate_den_mono (k : ℕ) (s : Core) (hOrder : s.denominator≤s.numerator) : s.previousDen≤(iterate k s).previousDen := by
  induction k generalizing s with
  | zero => exact le_rfl
  | succ k ih => exact (step_den_mono s hOrder).trans (ih (step s) (step_order s hOrder))

theorem future_den_ge_step (s : Core) (k : ℕ) (hOrder : s.denominator≤s.numerator) : (step s).previousDen≤(future s k).2 :=
  iterate_den_mono k (step s) (step_order s hOrder)

end Blotto.GeneralPaperCFModelOrder
