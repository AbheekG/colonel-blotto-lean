import Blotto.GeneralPaperRayClosedAffine

/-! The residual of an actual original high-tuple inequality at a fixed
budget. Its rational affine coefficients are literal field-anchor sums.
Open-interval feasibility extends to both closed endpoints exactly.
-/
namespace Blotto.GeneralPaperRayTupleResidual
open RationalOrderCell GeneralPaperRayAffine GeneralPaperRayAnchorCosts GeneralPaperRayHighSound
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

def residual {m K : ℕ} (x w : Variable m K → ℚ) (beta : ℚ) (labels : Fin m → Fin K) : Affine :=
  ⟨beta-(∑ j,anchorQ x j (labels j)),-(∑ j,anchorQ w j (labels j))⟩

theorem residual_value {m K : ℕ} (x w : Variable m K → ℚ) (beta t : ℚ) (labels : Fin m → Fin K) :
    (residual x w beta labels).value t=beta-(∑ j,costs x w t j (labels j)) := by
  rw [tuple_affine]
  dsimp only [residual,Affine.value]
  ring

theorem feasible_iff {m K : ℕ} (x w : Variable m K → ℚ) (beta t : ℚ) (labels : Fin m → Fin K) :
    (residual x w beta labels).value t≤0 ↔ beta≤∑ j,costs x w t j (labels j) := by
  rw [residual_value]
  exact sub_nonpos

theorem high_closed {m K : ℕ} (scores : Fin m → Fin K → ℕ) (x w : Variable m K → ℚ)
    (h : ℕ) (beta lo hi : ℚ) (hOrder : lo<hi)
    (hOpen : ∀ t,lo<t ∧ t<hi → HighFeasible scores (costs x w t) h beta) :
    HighFeasible scores (costs x w lo) h beta ∧ HighFeasible scores (costs x w hi) h beta := by
  have hh (labels : Fin m → Fin K) (hl : h<∑ j,scores j (labels j)) :=
    GeneralPaperRayClosedAffine.nonpositive_closed (residual x w beta labels) lo hi hOrder
      (fun t ht => (feasible_iff x w beta t labels).mpr (hOpen t ht labels hl))
  exact ⟨fun labels hl => (feasible_iff x w beta lo labels).mp (hh labels hl).1,
    fun labels hl => (feasible_iff x w beta hi labels).mp (hh labels hl).2⟩

end Blotto.GeneralPaperRayTupleResidual
