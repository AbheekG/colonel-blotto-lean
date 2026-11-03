import Blotto.NaturalPolynomialEnvelope
import Blotto.PlayerSpecificAlgebraicHeightEnvelope

/-! Elementary polynomial closure for the fixed algebraic-height iterations
used by the measured source-cost formulas. -/
namespace Blotto.PlayerSpecificSourcePolynomialAutomation
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem step_envelope {α : Type*} {size f : α → ℕ}
    (hf : NaturalPolynomialEnvelope size f) :
    NaturalPolynomialEnvelope size (fun x => step (f x)) := by
  unfold step
  exact NaturalPolynomialEnvelope.mul
    (NaturalPolynomialEnvelope.constant size coefficient)
    (NaturalPolynomialEnvelope.add hf (NaturalPolynomialEnvelope.constant size 1))

theorem iterate_envelope {α : Type*} {size f : α → ℕ}
    (hf : NaturalPolynomialEnvelope size f) (k : ℕ) :
    NaturalPolynomialEnvelope size (fun x => iterate k (f x)) := by
  induction k with
  | zero => simpa only [iterate] using hf
  | succ k ih =>
    change NaturalPolynomialEnvelope size (fun x => step (iterate k (f x)))
    exact step_envelope ih

end Blotto.PlayerSpecificSourcePolynomialAutomation
