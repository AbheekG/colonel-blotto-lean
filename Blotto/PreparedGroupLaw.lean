import Blotto.PreparedGroupOutput
import Blotto.ProportionalCDF
import Blotto.RationalMachineOutputMap

/-! Whole-law and marginal-error refinement of retained native routing
outputs, for arbitrary rational group laws and state-machine continuations. -/

namespace Blotto
open MeasureTheory

noncomputable def rationalAllocationLaw {m : ℕ} (μ : ProbabilityMeasure (Fin m → ℚ)) : Mixed m :=
  μ.map (fun y j => (y j : ℝ))

namespace PreparedGroupOutput

noncomputable def emitLaw {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (μ : ProbabilityMeasure (Fin m → ℚ)) : Mixed n := μ.map (fun y => (p.emit y).realAllocation)

noncomputable def emitMixedLaw {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (pivot : Fin n) (μ : ProbabilityMeasure (Fin (m + 1) → ℚ)) : Mixed n :=
  μ.map (fun y => (p.emitMixed pivot y).realAllocation)

theorem emitLaw_eq {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (μ : ProbabilityMeasure (Fin m → ℚ)) : p.emitLaw μ = G.real.splitLaw (rationalAllocationLaw μ) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun y => (p.emit y).realAllocation) (μ : Measure (Fin m → ℚ)) =
    Measure.map G.real.split (Measure.map (fun y j => (y j : ℝ)) (μ : Measure (Fin m → ℚ)))
  rw [Measure.map_map G.real.measurable_split (measurable_of_countable _)]
  congr 1
  exact funext p.emit_real

theorem emitMixedLaw_eq {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (pivot : Fin n) (μ : ProbabilityMeasure (Fin (m + 1) → ℚ)) :
    p.emitMixedLaw pivot μ = G.real.splitMixedLaw pivot (rationalAllocationLaw μ) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun y => (p.emitMixed pivot y).realAllocation) (μ : Measure (Fin (m + 1) → ℚ)) =
    Measure.map (G.real.splitMixed pivot) (Measure.map (fun y j => (y j : ℝ)) (μ : Measure (Fin (m + 1) → ℚ)))
  rw [Measure.map_map (G.real.measurable_splitMixed pivot) (measurable_of_countable _)]
  congr 1
  exact funext (p.emitMixed_real pivot)

theorem emitLaw_CDFClose {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (μ : ProbabilityMeasure (Fin m → ℚ)) (ν : Mixed m) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : CDFClose (rationalAllocationLaw μ) ν δ) : CDFClose (p.emitLaw μ) (G.real.splitLaw ν) δ := by
  rw [p.emitLaw_eq]
  exact G.real.splitLaw_CDFClose _ _ hδ h

theorem emitMixedLaw_CDFClose {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G)
    (pivot : Fin n) (hp : ∀ g, pivot ∉ G.members g) (μ : ProbabilityMeasure (Fin (m + 1) → ℚ))
    (ν : Mixed (m + 1)) {δ : ℝ} (h : CDFClose (rationalAllocationLaw μ) ν δ) :
    CDFClose (p.emitMixedLaw pivot μ) (G.real.splitMixedLaw pivot ν) δ := by
  rw [p.emitMixedLaw_eq]
  exact G.real.splitMixedLaw_CDFClose pivot (by simpa [RationalProportionalGroups.real] using hp) _ _ h

theorem machineIdealLaw_eq {S : Type*} {n m : ℕ} {G : RationalProportionalGroups n m}
    (p : PreparedGroupOutput G) (controller : WordStateMachine S (Fin m → ℚ)) (s : S) :
    (controller.mapped (fun y => (p.emit y).allocation)).rationalIdealLaw s =
      G.real.splitLaw (controller.rationalIdealLaw s) :=
  controller.rationalIdealLaw_map_refines _ _ G.real.measurable_split p.emit_real s

theorem machineMixedIdealLaw_eq {S : Type*} {n m : ℕ} {G : RationalProportionalGroups n m}
    (p : PreparedGroupOutput G) (pivot : Fin n) (controller : WordStateMachine S (Fin (m + 1) → ℚ)) (s : S) :
    (controller.mapped (fun y => (p.emitMixed pivot y).allocation)).rationalIdealLaw s =
      G.real.splitMixedLaw pivot (controller.rationalIdealLaw s) :=
  controller.rationalIdealLaw_map_refines _ _ (G.real.measurable_splitMixed pivot) (p.emitMixed_real pivot) s

end PreparedGroupOutput
end Blotto
