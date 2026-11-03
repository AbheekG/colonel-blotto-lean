import Blotto.RationalMachineLaw

/-! Output refinement for any native rational emitter with a measurable real
interpretation. This includes cached sparse routes without a dense matrix. -/

namespace Blotto
open MeasureTheory

namespace WordStateMachine

theorem rationalIdealLaw_map_refines {S : Type*} {n m : ℕ} (controller : WordStateMachine S (Fin n → ℚ))
    (f : (Fin n → ℚ) → (Fin m → ℚ)) (F : Allocation n → Allocation m) (hF : Measurable F)
    (hf : ∀ x, (fun j => (f x j : ℝ)) = F (fun j => (x j : ℝ))) (s : S) :
    (controller.mapped f).rationalIdealLaw s = (controller.rationalIdealLaw s).map F := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro A hA
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((controller.mapped f).rationalIdealLaw s : Measure (Allocation m)).real A =
    (Measure.map F (controller.rationalIdealLaw s : Measure (Allocation n))).real A
  rw [rationalIdealLaw_event _ _ A hA, mapped_mean,
    map_measureReal_apply hF hA, controller.rationalIdealLaw_event s _ (hA.preimage hF)]
  congr 1
  funext x
  rw [hf]
  rfl

end WordStateMachine
end Blotto
