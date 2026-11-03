import Blotto.GeneralPaperAllBranchExactRealLaw

/-! Sampling contracts on the actual tagged real-RAM preparation return.
Costs include output writes. Independence concerns whole-player seeds. -/
namespace Blotto.GeneralPaperAllBranchExactRealSampling
open MeasureTheory
open GeneralPaperOriginalRealInput GeneralPaperAllBranchRealDispatch
open GeneralPaperAllBranchRealLaw (law)
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def Contract (model : RationalCostModel) (p : Input) : Prepared model p → Prop
  | .oneField h rich poor =>
      (∀ row ∈ [rich, poor],
        (GeneralPaperOneFieldRealPreparation.draw row).uniformReads = 0 ∧
        (GeneralPaperOneFieldRealPreparation.draw row).bitReads = 0 ∧
        (GeneralPaperOneFieldRealPreparation.draw row).work = 21 ∧
        (GeneralPaperOneFieldRealPreparation.draw row).output.read = row.realAllocation) ∧
      Measure.map (fun _ : Fin 0 → Bool =>
        (h.symm ▸ (GeneralPaperOneFieldRealPreparation.draw rich).output.read,
         h.symm ▸ (GeneralPaperOneFieldRealPreparation.draw poor).output.read))
        (fairBitLaw 0 : Measure (Fin 0 → Bool)) =
        (law model p (.oneField h rich poor) false : Measure (Allocation p.n)).prod
          (law model p (.oneField h rich poor) true : Measure (Allocation p.n))
  | .equal k source =>
      (GeneralPaperEqualRealBranchDraw.seedLaw (k + 5)).map
        (fun z => (GeneralPaperEqualRealBranchDraw.run source z.1 z.2).output.read) =
          GeneralPaperEqualRealBranch.outputLaw source ∧
      (let μ := (GeneralPaperEqualRealBranchDraw.seedLaw (k + 5) : Measure (ℝ × (Fin (k + 5) → Bool)))
       let f := fun z : ℝ × (Fin (k + 5) → Bool) =>
         (GeneralPaperEqualRealBranchDraw.run source z.1 z.2).output.read
       Measure.map (Prod.map f f) (μ.prod μ) =
         (law model p (.equal k source) false : Measure (Allocation p.n)).prod
           (law model p (.equal k source) true : Measure (Allocation p.n))) ∧
      ∀ u fresh,
        (GeneralPaperEqualRealBranchDraw.run source u fresh).work ≤
          2048 * (p.n + binaryWordWidth ⌈p.epsilon⁻¹⌉₊) ∧
        (GeneralPaperEqualRealBranchDraw.run source u fresh).uniformReads ≤ 1 ∧
        (GeneralPaperEqualRealBranchDraw.run source u fresh).bitReads ≤ binaryWordWidth ⌈p.epsilon⁻¹⌉₊ + 5
  | .unequal output => output.sampler.elim False (fun sampler =>
      (∀ reciprocal fresh,
        (GeneralPaperExactStoredSampler.run false (fun _ => 1) 1 model sampler reciprocal fresh).work ≤
          131072 * (p.n + binaryWordWidth ⌈p.epsilon⁻¹⌉₊) ∧
        (GeneralPaperExactStoredSampler.run false (fun _ => 1) 1 model sampler reciprocal fresh).freshReads =
          Nat.log2 (sampler.controls.rows * GeneralPaperExactStoredSampler.shifts sampler)) ∧
      (let D := GeneralPaperExactStoredSampler.bits sampler
       Measure.map (fun fresh =>
         ((fun j => ((GeneralPaperExactStoredSampler.run false (fun _ => 1) 1 model sampler false
             (firstBitBlock D D fresh)).output.read j : ℝ)),
          (fun j => ((GeneralPaperExactStoredSampler.run false (fun _ => 1) 1 model sampler true
             (secondBitBlock D D fresh)).output.read j : ℝ))))
         (fairBitLaw (D + D) : Measure (Fin (D + D) → Bool)) =
         (GeneralPaperStoredStrategySampler.law false (fun _ => 1) 1 model sampler false : Measure (Allocation p.n)).prod
           (GeneralPaperStoredStrategySampler.law false (fun _ => 1) 1 model sampler true : Measure (Allocation p.n))))

theorem one_contract (model : RationalCostModel) (p : Input) (hN : p.n = 1) :
    Contract model p (one model p hN).1 := by
  constructor
  · intro row _
    exact ⟨(GeneralPaperOneFieldRealPreparation.draw_resources row).1,
      (GeneralPaperOneFieldRealPreparation.draw_resources row).2.1,
      (GeneralPaperOneFieldRealPreparation.draw_resources row).2.2,
      GeneralPaperOneFieldRealPreparation.draw_data row⟩
  · rcases p with ⟨n, values, selector, correct, eps, hEps, b, hBudget⟩
    change n = 1 at hN
    subst n
    change Measure.map (fun _ : Fin 0 → Bool =>
      ((GeneralPaperOneFieldRealPreparation.draw _).output.read,
       (GeneralPaperOneFieldRealPreparation.draw _).output.read)) _ = _
    rw [GeneralPaperOneFieldRealPreparation.draw_data, GeneralPaperOneFieldRealPreparation.draw_data,
      Measure.map_const, measure_univ, one_smul]
    exact Measure.dirac_prod_dirac.symm

theorem equal_contract (model : RationalCostModel) (p : Input) :
    Contract model p (equal model p).1 := by
  refine ⟨GeneralPaperEqualRealBranchDraw.law _, GeneralPaperEqualRealBranchDraw.independent_players _, ?_⟩
  intro u fresh
  have h := GeneralPaperEqualRealDispatchContract.paper_contract model p.epsilon
    p.epsilon_valid.1 p.epsilon_valid.2 p.values p.selector p.correct p.budget p.budget_valid.1
  have hd := h.2.2.2.2 u fresh
  have hn := p.selector.fields_positive
  exact ⟨hd.2.1.trans (by omega), hd.2.2⟩

theorem unequal_contract (model : RationalCostModel) (p : Input) (hB : p.budget < 1) :
    Contract model p (unequal model p).1 := by
  obtain ⟨sampler, hSampler, _⟩ := GeneralPaperClosedStrategyEquilibrium.arithmetic_epsilon model
    p.epsilon p.epsilon_valid.1 p.epsilon_valid.2 p.values p.selector p.correct p.budget
      ⟨p.budget_valid.1, hB⟩ (fun _ => 1)
  dsimp only [Contract, unequal]
  simp only [hSampler, Option.elim_some]
  refine ⟨fun reciprocal fresh => ⟨?_, GeneralPaperExactPreparationDraw.logarithmic_control_bits
    false (fun _ => 1) 1 model sampler reciprocal fresh⟩,
      GeneralPaperExactStoredSampler.independent_players false (fun _ => 1) 1 model sampler⟩
  exact GeneralPaperExactRealSampler.arithmetic_draw_work model p.epsilon p.values p.selector p.correct
    p.budget ⟨p.budget_valid.1, hB⟩ sampler hSampler reciprocal fresh

theorem actual_contract (model : RationalCostModel) (p : Input) : Contract model p (run model p).1 := by
  by_cases hN : p.n = 1
  · rw [on_one model p hN]
    exact one_contract model p hN
  · by_cases hB : p.budget = 1
    · rw [on_equal model p hN hB]
      exact equal_contract model p
    · rw [on_unequal model p hN hB]
      exact unequal_contract model p (strict_of_ne p hB)

theorem time_game_and_sampling (model : RationalCostModel) :
    ∃ C d : ℕ, ∀ p : Input, ((run model p).2 : ℚ) ≤
      (C : ℚ) * GeneralPaperRealHeadlineParameters.timeScale p.n p.epsilon *
        (GeneralPaperRealHeadlineParameters.logarithm p.n p.epsilon : ℚ) ^ d ∧
      GeneralPaperAllBranchExactRealLaw.Guarantee model p (run model p).1 ∧
      GeneralPaperAllBranchExactRealLaw.Pointwise model p (run model p).1 ∧
      Contract model p (run model p).1 := by
  obtain ⟨C, d, h⟩ := GeneralPaperAllBranchRealTime.time_and_original_game_contract model
  exact ⟨C, d, fun p => ⟨(h p).1,
    GeneralPaperAllBranchExactRealLaw.guarantee_of_reference model p _ (h p).2.1,
    GeneralPaperAllBranchExactRealLaw.pointwise_of_reference model p _ (h p).2.1 (h p).2.2,
    actual_contract model p⟩⟩

end Blotto.GeneralPaperAllBranchExactRealSampling
