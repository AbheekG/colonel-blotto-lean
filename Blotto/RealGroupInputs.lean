import Blotto.RealFourSampler

/-! Small grouped draws reuse projections of the fixed independent packet.
The unit and nine-input projections have their actual continuous laws. -/

namespace Blotto
open MeasureTheory

def realGroupUnit (seed : RealFourSeed) : ℝ := seed.1 0
def realGroupThreeSeed (seed : RealFourSeed) : Fin 9 → ℝ := RealUniformInputs.dropInputs 9 72 seed.1

def realGroupSeedValid (seed : RealFourSeed) : Prop :=
  (∀ j, 0 ≤ seed.1 j ∧ seed.1 j ≤ 1) ∧ (∀ j, 0 ≤ seed.2.2.2 j ∧ seed.2.2.2 j ≤ 1)

theorem realGroupUnit_measurable : Measurable realGroupUnit := (measurable_pi_apply 0).comp measurable_fst

theorem realGroupThreeSeed_measurable : Measurable realGroupThreeSeed :=
  (RealUniformInputs.dropInputs_measurable 9 72).comp
    (measurable_fst : Measurable (Prod.fst : RealFourSeed → (Fin 81 → ℝ)))

theorem realGroupUnit_law :
    Measure.map realGroupUnit (FourInput.realInputLaw : Measure RealFourSeed) = (unitUniform : Measure ℝ) := by
  change Measure.map ((fun seed : Fin 81 → ℝ => seed 0) ∘ (Prod.fst : RealFourSeed → (Fin 81 → ℝ)))
    ((RealUniformInputs.law 81 : Measure (Fin 81 → ℝ)).prod
      (FourInput.realSmallInputLaw : Measure (ℝ × ((Fin 2 → ℝ) × (Fin 11 → ℝ))))) = _
  rw [← Measure.map_map (measurable_pi_apply 0) measurable_fst, Measure.map_fst_prod,
    measure_univ, one_smul, RealUniformInputs.head_law 80]

theorem realGroupThreeSeed_law :
    Measure.map realGroupThreeSeed (FourInput.realInputLaw : Measure RealFourSeed) =
      (RealUniformInputs.law 9 : Measure (Fin 9 → ℝ)) := by
  change Measure.map (RealUniformInputs.dropInputs 9 72 ∘ (Prod.fst : RealFourSeed → (Fin 81 → ℝ)))
    ((RealUniformInputs.law 81 : Measure (Fin 81 → ℝ)).prod
      (FourInput.realSmallInputLaw : Measure (ℝ × ((Fin 2 → ℝ) × (Fin 11 → ℝ))))) = _
  rw [← Measure.map_map (RealUniformInputs.dropInputs_measurable 9 72) measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul, RealUniformInputs.dropInputs_law 9 72]

theorem realGroupThreeSeed_bounds (seed : RealFourSeed) (h : realGroupSeedValid seed) :
    ∀ j, 0 ≤ realGroupThreeSeed seed j ∧ realGroupThreeSeed seed j ≤ 1 :=
  RealUniformInputs.dropInputs_bounds 9 72 seed.1 h.1

end Blotto
