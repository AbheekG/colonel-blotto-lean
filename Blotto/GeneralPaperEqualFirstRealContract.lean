import Blotto.GeneralPaperEqualFirstHeights

/-! One actual c=256 equal-budget real return joins original-game
accuracy, bounded preparation, pointwise full-budget draws, the exact
sampling law and independent whole-player seeds. -/
namespace Blotto.GeneralPaperEqualFirstRealContract
open MeasureTheory
open GeneralPaperEqualRealBranch (outputLaw)
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem paper_contract {n : ℕ} (model : RationalCostModel) (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (hB : 0 < budget) :
    let result := GeneralPaperEqualFirstRealDispatch.accuracy model eps values v hv budget
    result.2 ≤ 67108864 * (n + 1) * (binaryWordWidth n + binaryWordWidth ⌈eps⁻¹⌉₊ + 16) ^ 2 ∧
    Supported (budget : ℝ) (outputLaw result.1) ∧
    regret v.values (budget : ℝ) (outputLaw result.1) (outputLaw result.1) ≤ (eps : ℝ) ∧
    expected v.values (outputLaw result.1) (outputLaw result.1) = 1 / 2 ∧
    ∀ u fresh,
      FullBudget (budget : ℝ) (GeneralPaperEqualRealBranchDraw.run result.1 u fresh).output.read ∧
      (GeneralPaperEqualRealBranchDraw.run result.1 u fresh).work ≤ 1024 * (n + binaryWordWidth ⌈eps⁻¹⌉₊ + 1) ∧
      (GeneralPaperEqualRealBranchDraw.run result.1 u fresh).uniformReads ≤ 1 ∧
      (GeneralPaperEqualRealBranchDraw.run result.1 u fresh).bitReads ≤ binaryWordWidth ⌈eps⁻¹⌉₊ + 5 := by
  let result := GeneralPaperEqualFirstRealDispatch.accuracy model eps values v hv budget
  have he := GeneralPaperEqualFirstRealDispatch.epsilon model eps hp hOne values v hv budget hB
  refine ⟨GeneralPaperEqualFirstRealDispatch.accuracy_work model eps values v hv budget, he.1, he.2,
    GeneralPaperEqualRealBranch.expected_half result.1 v.values, fun u fresh => ?_⟩
  have hw := GeneralPaperEqualRealBranchDraw.work result.1 u fresh
  have hr := GeneralPaperEqualRealBranchDraw.reads result.1 u fresh
  have ha := GeneralPaperDyadicAccuracy.prepare_work eps
  have hex := GeneralPaperDyadicAccuracy.prepare_work_exact eps
  exact ⟨GeneralPaperEqualRealBranchDraw.hard_budget result.1 hB.le u fresh,
    hw.trans (by omega), hr.1, hr.2.trans (by omega)⟩

theorem actual_output_law {n : ℕ} (model : RationalCostModel) (eps : ℚ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) :
    let p := (GeneralPaperEqualFirstRealDispatch.accuracy model eps values v hv budget).1
    (GeneralPaperEqualRealBranchDraw.seedLaw ((GeneralPaperDyadicAccuracy.prepare eps).exponent + 5)).map
      (fun z => (GeneralPaperEqualRealBranchDraw.run p z.1 z.2).output.read) = outputLaw p :=
  GeneralPaperEqualRealBranchDraw.law _

theorem independent_players {n : ℕ} (model : RationalCostModel) (eps : ℚ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) :
    let p := (GeneralPaperEqualFirstRealDispatch.accuracy model eps values v hv budget).1
    let K := (GeneralPaperDyadicAccuracy.prepare eps).exponent + 5
    let μ := (GeneralPaperEqualRealBranchDraw.seedLaw K : Measure (ℝ × (Fin K → Bool)))
    let f := fun z : ℝ × (Fin K → Bool) => (GeneralPaperEqualRealBranchDraw.run p z.1 z.2).output.read
    Measure.map (Prod.map f f) (μ.prod μ) =
      (outputLaw p : Measure (Allocation n)).prod (outputLaw p : Measure (Allocation n)) :=
  GeneralPaperEqualRealBranchDraw.independent_players _

end Blotto.GeneralPaperEqualFirstRealContract
