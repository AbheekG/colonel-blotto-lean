import Blotto.GeneralPaperMixedInitializerCalibration
import Blotto.GeneralPaperEqualRealDispatchContract

/-! Numeric real-primitive input. Accuracy is supplied as a rational value;
the real producer does not traverse its binary encoding. The binary view
below is an erased correspondence observer. -/
namespace Blotto.GeneralPaperOriginalRealInput
set_option autoImplicit false

structure Input where
  n : ℕ
  values : FixedArrayTable n ℚ
  selector : RationalFieldSelector n
  correct : ∀ j, values.read j = selector.weight j
  epsilon : ℚ
  epsilon_valid : 0 < epsilon ∧ epsilon < 1
  budget : ℚ
  budget_valid : 0 < budget ∧ budget ≤ 1

def ofBinary (p : GeneralPaperOriginalGameInput.Input) (hOne : GeneralPaperOriginalGameInput.epsilon p < 1) : Input :=
  ⟨p.n, p.values, p.selector, p.correct, GeneralPaperOriginalGameInput.epsilon p,
    ⟨GeneralPaperOriginalGameInput.epsilon_positive p, hOne⟩, p.budget, p.budget_valid⟩

theorem fields_positive (p : Input) : 0 < p.n := p.selector.fields_positive

theorem strict_of_ne (p : Input) (h : p.budget ≠ 1) : p.budget < 1 := lt_of_le_of_ne p.budget_valid.2 h

end Blotto.GeneralPaperOriginalRealInput
