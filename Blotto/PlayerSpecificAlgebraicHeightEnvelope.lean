import Blotto.PlayerSpecificAlgebraicInitialContract

/-! One linear coefficient envelope covers the actual fixed-degree reduce,
constant, inverse, product and quotient implementations. It is an analysis
bound for computed outputs, not an input to any algebraic runtime operation. -/
namespace Blotto.PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificPolynomialNormalization
open PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := PlayerSpecificAlgebraicInverseContract.heightCoefficient+
  PlayerSpecificFieldDivisionContract.heightCoefficient+1000000^3+50002
def step (H : ℕ) : ℕ := coefficient*(H+1)
def iterate : ℕ → ℕ → ℕ | 0,H => H | k+1,H => step (iterate k H)

theorem calibrate (C H : ℕ) (hC : C≤coefficient) : C*(H+1)≤step H := Nat.mul_le_mul_right _ hC
theorem large (H : ℕ) : H+1≤step H := by
  have hp:=calibrate 1 H (by unfold coefficient; omega)
  simpa only [Nat.one_mul] using hp
theorem mono : Monotone step := by
  intro H J h
  exact Nat.mul_le_mul_left coefficient (Nat.add_le_add_right h 1)
theorem iterate_bound (k H : ℕ) : iterate k H+1≤(coefficient+1)^k*(H+1) := by
  induction k with
  | zero => simp only [iterate,pow_zero,Nat.one_mul,Nat.le_refl]
  | succ k ih =>
    have hstep : coefficient*(iterate k H+1)+1≤(coefficient+1)*(iterate k H+1) := by nlinarith
    have hm:=Nat.mul_le_mul_left (coefficient+1) ih
    simp only [iterate,step,pow_succ]
    exact hstep.trans (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hm)

theorem reduce_height (m a : Data) (H : ℕ) (hm : HasHeight m H) (ha : HasHeight a H)
    (hH : 1≤H) (hml : m.length≤4) (hal : a.length≤4) : HasHeight (reduce m a) (step H) := by
  have hh:=(PlayerSpecificDivisionHeights.run_height a m H ha hm hH hal hml).2
  apply PlayerSpecificPolynomialHeights.mono hh
  have hc:=calibrate 50000 H (by unfold coefficient; omega)
  rw [PlayerSpecificDivisionHeights.linear]
  omega

theorem constant_height (m : Data) (q : ℚ) (H : ℕ) (hm : HasHeight m H) (hq : RationalHeight q H)
    (hH : 1≤H) (hml : m.length≤4) : HasHeight (PlayerSpecificAlgebraicField.constant m q) (step H) :=
  reduce_height m [q] H hm (cons_height hq (nil_height _)) hH hml (by simp)

theorem inverse_height (m a : Data) (H : ℕ) (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4)
    (ha : Reduced m a) (hmH : HasHeight m H) (haH : HasHeight a H) (hH : 1≤H) :
    HasHeight (PlayerSpecificAlgebraicField.inverse m a) (step H) := by
  have hh:=(PlayerSpecificAlgebraicInverseExecution.bounds RationalCostModel.schoolbook m a hm hm0 hml ha H hmH haH hH).1
  rw [PlayerSpecificAlgebraicInverseExecution.value] at hh
  exact PlayerSpecificPolynomialHeights.mono hh ((PlayerSpecificAlgebraicInverseContract.height_linear H).trans
    (calibrate _ H (by unfold coefficient; omega)))

theorem times_height (m a b : Data) (H : ℕ) (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4)
    (ha : Reduced m a) (hb : Reduced m b) (hmH : HasHeight m H) (haH : HasHeight a H) (hbH : HasHeight b H) :
    HasHeight (PlayerSpecificAlgebraicField.times m a b) (step H) := by
  have hal : a.length≤3 := by have hl:=ha.2; omega
  have hbl : b.length≤3 := by have hl:=hb.2; omega
  have hh:=PlayerSpecificModularHeights.run_height m b a hm hm0 hml hbl H hmH hbH haH
  have hf:=PlayerSpecificModularHeights.fuel_mono H hal
  exact PlayerSpecificPolynomialHeights.mono hh (hf.trans (calibrate (1000000^3) H (by unfold coefficient; omega)))

theorem divide_height (m a b : Data) (H : ℕ) (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4)
    (ha : Reduced m a) (hb : Reduced m b) (hmH : HasHeight m H) (haH : HasHeight a H) (hbH : HasHeight b H) (hH : 1≤H) :
    HasHeight (PlayerSpecificAlgebraicField.divide m a b) (step H) := by
  have hh:=(PlayerSpecificFieldDivisionExecution.bounds RationalCostModel.schoolbook m a b hm hm0 hml ha hb H hmH haH hbH hH).2.2
  rw [PlayerSpecificFieldDivisionExecution.value] at hh
  exact PlayerSpecificPolynomialHeights.mono hh ((PlayerSpecificFieldDivisionContract.height_linear H).trans
    (calibrate _ H (by unfold coefficient; omega)))

end Blotto.PlayerSpecificAlgebraicHeightEnvelope
