import Blotto.GeneralPaperRealSegmentPrimitives

/-! Same-return contracts for the complete smaller-cache real preparation
and its direct draw. The noncomputable view is used only inside proofs; the
producer and draw never construct categorical integer or Boolean data. -/
namespace Blotto.GeneralPaperEqualRealContract
open MeasureTheory
open GeneralPaperEqualNativeSampler (rounded)
open GeneralPaperEqualRealPreparation (run data)
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem law {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded false model 1 k values v hv).weight j ≤ 1) (budget : ℚ) :
    GeneralPaperEqualRealCacheDraw.outputLaw (run model k values v hv small budget).1 =
      GeneralPaperEqualRealDraw.outputLaw (GeneralPaperEqualNativeCache.prepare false model 1 k values v hv small budget) := by
  rw [GeneralPaperEqualRealCacheDraw.outputLaw_eq, data, GeneralPaperEqualRealCache.view_project]

theorem draw_work {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded false model 1 k values v hv).weight j ≤ 1) (budget : ℚ) :
    let cache := (run model k values v hv small budget).1
    ∀ u fresh, (GeneralPaperEqualRealCacheDraw.run cache u fresh).work ≤ 1024 * (n + k + 1) := by
  dsimp only
  rw [data]
  intro u fresh
  rw [GeneralPaperEqualRealCacheDraw.run_eq_view]
  exact GeneralPaperEqualRealSamplingContract.native_work false model 1 k values v hv small budget u fresh

theorem epsilon {n : ℕ} (model : RationalCostModel) (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded false model 1 (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1)
    (budget : ℚ) (hB : 0 < budget) :
    let cache := (GeneralPaperEqualRealPreparationRates.run model eps values v hv small budget).1
    Supported (budget : ℝ) (GeneralPaperEqualRealCacheDraw.outputLaw cache) ∧
      regret v.values (budget : ℝ) (GeneralPaperEqualRealCacheDraw.outputLaw cache)
        (GeneralPaperEqualRealCacheDraw.outputLaw cache) ≤ (eps : ℝ) := by
  dsimp only [GeneralPaperEqualRealPreparationRates.run]
  rw [law]
  exact GeneralPaperEqualRealSamplingContract.native_epsilon false model 1 values v hv eps hp hOne small budget hB

theorem written_output {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded false model 1 k values v hv).weight j ≤ 1)
    (budget : ℚ) (hB : 0 ≤ budget) {b : ℕ} (height : RationalHeight budget b) :
    let cache := (run model k values v hv small budget).1
    ∀ u fresh, ∃ row : RationalResourceArray n,
      (GeneralPaperEqualRealCacheDraw.run cache u fresh).output.read = row.realAllocation ∧
      FullBudget (budget : ℝ) row.realAllocation ∧
      ∀ j, RationalHeight (row.allocation j) (33554432 * (b + binaryWordWidth n + k + 10)) := by
  dsimp only
  rw [data]
  intro u fresh
  rw [GeneralPaperEqualRealCacheDraw.run_eq_view]
  exact GeneralPaperEqualRealSamplingContract.native_output false model 1 k values v hv small budget hB height u fresh

theorem paper_contract {n : ℕ} (model : RationalCostModel) (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded false model 1 (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1)
    (budget : ℚ) (hB : 0 < budget) :
    let result := GeneralPaperEqualRealPreparationRates.run model eps values v hv small budget
    result.2 ≤ 8388608 * (n + 1) * (binaryWordWidth n + binaryWordWidth ⌈eps⁻¹⌉₊ + 16) ^ 2 ∧
    Supported (budget : ℝ) (GeneralPaperEqualRealCacheDraw.outputLaw result.1) ∧
    regret v.values (budget : ℝ) (GeneralPaperEqualRealCacheDraw.outputLaw result.1)
      (GeneralPaperEqualRealCacheDraw.outputLaw result.1) ≤ (eps : ℝ) ∧
    (∀ u fresh, (GeneralPaperEqualRealCacheDraw.run result.1 u fresh).work ≤
      1024 * (n + binaryWordWidth ⌈eps⁻¹⌉₊ + 1)) := by
  have hRegret := epsilon model eps hp hOne values v hv small budget hB
  refine ⟨GeneralPaperEqualRealPreparationRates.work model eps values v hv small budget,
    hRegret.1, hRegret.2, fun u fresh => ?_⟩
  have h := draw_work model (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget u fresh
  have ha := GeneralPaperDyadicAccuracy.prepare_work eps
  have he := GeneralPaperDyadicAccuracy.prepare_work_exact eps
  exact h.trans (by omega)

end Blotto.GeneralPaperEqualRealContract
