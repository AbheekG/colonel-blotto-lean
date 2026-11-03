import Blotto.GeneralPaperSecurityCounterexample
import Blotto.Mixed

/-! The nearby pure A allocations defeat every budget-supported mixed
B response, using the actual two-player whole-allocation mixed model. -/
namespace Blotto.GeneralPaperSecurityCounterexampleMixed
open MeasureTheory
open GeneralPaperSecurityCounterexample
set_option autoImplicit false

theorem every_mixed_B_loses (t : ℝ) (ht : 0<t ∧ t<1/3)
    (nu : Mixed 2) (hnu : Supported (1/3:ℝ) nu) :
    (∫ y, payoff values y (xMove t) ∂(nu : Measure (Allocation 2)))=0 := by
  have hae : (fun y => payoff values y (xMove t)) =ᵐ[(nu : Measure (Allocation 2))]
      (fun _ => (0:ℝ)) := by
    filter_upwards [hnu] with y hy
    exact (moved_dominates t ht y hy).2
  rw [integral_congr_ae hae]
  simp

theorem every_mixed_B_loses_payoff (t : ℝ) (ht : 0<t ∧ t<1/3)
    (nu : Mixed 2) (hnu : Supported (1/3:ℝ) nu) :
    (∫ y, payoff values (xMove t) y ∂(nu : Measure (Allocation 2)))=1 := by
  have hae : (fun y => payoff values (xMove t) y) =ᵐ[(nu : Measure (Allocation 2))]
      (fun _ => (1:ℝ)) := by
    filter_upwards [hnu] with y hy
    exact (moved_dominates t ht y hy).1
  rw [integral_congr_ae hae]
  simp

end Blotto.GeneralPaperSecurityCounterexampleMixed
