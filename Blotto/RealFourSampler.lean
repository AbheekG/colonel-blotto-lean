import Blotto.RealFourGluing
import Blotto.RealFourSmall
import Blotto.FourSpec

/-! Both exact continuous four-variable constructions share independent
input blocks. The sorted specification then restores original coordinates.
The fixed packet size is an interface bound, not a full primitive-cost proof. -/

namespace Blotto
open MeasureTheory
open scoped Classical

abbrev RealFourSeed := (Fin 81 → ℝ) × (ℝ × ((Fin 2 → ℝ) × (Fin 11 → ℝ)))

namespace FourInput

noncomputable def realInputLaw : ProbabilityMeasure RealFourSeed :=
  RealUniformInputs.productLaw (RealUniformInputs.law 81) realSmallInputLaw

noncomputable def realSample (i : FourInput) (seed : RealFourSeed) : Allocation 4 :=
  if hcase : (1 - i.p) * i.ell ≤ i.w then i.realGluingSample hcase seed.1
  else i.realSmallSample (lt_of_not_ge hcase) seed.2

theorem realSample_measurable (i : FourInput) : Measurable i.realSample := by
  change Measurable (fun seed => if hcase : (1 - i.p) * i.ell ≤ i.w then _ else _)
  by_cases hcase : (1 - i.p) * i.ell ≤ i.w
  · simp only [dite_eq_left hcase]
    exact (i.realGluingSample_measurable hcase).comp measurable_fst
  · simp only [dite_eq_right hcase]
    exact (i.realSmallSample_measurable (lt_of_not_ge hcase)).comp measurable_snd

theorem realSample_law (i : FourInput) :
    Measure.map i.realSample (realInputLaw : Measure RealFourSeed) = (i.law : Measure (Allocation 4)) := by
  change Measure.map (fun seed => if hcase : (1 - i.p) * i.ell ≤ i.w then _ else _) _ = _
  by_cases hcase : (1 - i.p) * i.ell ≤ i.w
  · simp only [law, dite_eq_left hcase]
    change Measure.map (i.realGluingSample hcase ∘ (Prod.fst : RealFourSeed → (Fin 81 → ℝ)))
      ((RealUniformInputs.law 81 : Measure (Fin 81 → ℝ)).prod
        (realSmallInputLaw : Measure (ℝ × ((Fin 2 → ℝ) × (Fin 11 → ℝ))))) = _
    rw [← Measure.map_map (i.realGluingSample_measurable hcase) measurable_fst,
      Measure.map_fst_prod, measure_univ, one_smul]
    exact i.realGluingSample_law hcase
  · simp only [law, dite_eq_right hcase]
    change Measure.map (i.realSmallSample (lt_of_not_ge hcase) ∘
      (Prod.snd : RealFourSeed → (ℝ × ((Fin 2 → ℝ) × (Fin 11 → ℝ)))))
      ((RealUniformInputs.law 81 : Measure (Fin 81 → ℝ)).prod
        (realSmallInputLaw : Measure (ℝ × ((Fin 2 → ℝ) × (Fin 11 → ℝ))))) = _
    rw [← Measure.map_map (i.realSmallSample_measurable (lt_of_not_ge hcase)) measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul]
    exact i.realSmallSample_law (lt_of_not_ge hcase)

theorem realSample_fullBudget (i : FourInput) (seed : RealFourSeed)
    (hG : 0 ≤ seed.1 0 ∧ seed.1 0 ≤ 1) (hN : ∀ j, 0 ≤ seed.2.2.2 j ∧ seed.2.2.2 j ≤ 1) :
    FullBudget i.B (i.realSample seed) := by
  unfold realSample
  split_ifs with hcase
  · exact i.realGluingSample_fullBudget hcase seed.1 hG
  · exact i.realSmallSample_fullBudget (lt_of_not_ge hcase) seed.2 hN

end FourInput
namespace FourSpec

noncomputable def realSample (i : FourSpec) (seed : RealFourSeed) : Allocation 4 :=
  permuteAllocation (permutationWithLast (sortTriplePermutation i.length)).symm (i.input.realSample seed)

theorem realSample_measurable (i : FourSpec) : Measurable i.realSample :=
  (measurable_permuteAllocation _).comp i.input.realSample_measurable

theorem realSample_law (i : FourSpec) :
    Measure.map i.realSample (FourInput.realInputLaw : Measure RealFourSeed) = (i.law : Measure (Allocation 4)) := by
  change Measure.map (permuteAllocation (permutationWithLast (sortTriplePermutation i.length)).symm ∘ i.input.realSample) _ = _
  rw [← Measure.map_map (measurable_permuteAllocation _) i.input.realSample_measurable, i.input.realSample_law]
  rfl

theorem realSample_fullBudget (i : FourSpec) (seed : RealFourSeed)
    (hG : 0 ≤ seed.1 0 ∧ seed.1 0 ≤ 1) (hN : ∀ j, 0 ≤ seed.2.2.2 j ∧ seed.2.2.2 j ≤ 1) :
    FullBudget i.B (i.realSample seed) :=
  permuteAllocation_fullBudget _ (i.input.realSample_fullBudget seed hG hN)

theorem realSample_marginals (i : FourSpec) :
    (∀ j : Fin 3, Measure.map (fun seed => i.realSample seed j.castSucc)
      (FourInput.realInputLaw : Measure RealFourSeed) = uniformLaw (i.length j)) ∧
      Measure.map (fun seed => i.realSample seed 3) (FourInput.realInputLaw : Measure RealFourSeed) = zeroUniformLaw i.ell i.p := by
  have hCoordinate (j : Fin 4) :
      Measure.map (fun seed => i.realSample seed j) (FourInput.realInputLaw : Measure RealFourSeed) =
        (marginal i.law j : Measure ℝ) := by
    change Measure.map ((fun x : Allocation 4 => x j) ∘ i.realSample) _ = _
    rw [← Measure.map_map (measurable_pi_apply j) i.realSample_measurable, i.realSample_law]
    rfl
  constructor
  · intro j
    rw [hCoordinate]
    exact i.law_contract.2.1 j
  · rw [hCoordinate]
    exact i.law_contract.2.2

end FourSpec
end Blotto
