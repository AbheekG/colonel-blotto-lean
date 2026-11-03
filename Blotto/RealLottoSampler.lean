import Blotto.RealLottoActivePhase
import Blotto.RealTerminalSampler
import Blotto.RealRoundingKernel

/-! The complete exact-real Lotto draw follows the maintained active source,
prepares the reached grouped terminal, and emits its allocation array. The
law proof uses the finite tree, while execution never constructs that tree. -/

namespace Blotto
open MeasureTheory
open scoped Classical

abbrev RealLottoSeed (n : ℕ) := (Fin (n - 1) → ℝ) × RealFourSeed

namespace LottoResourceSystem

noncomputable def realInputLaw (n : ℕ) : ProbabilityMeasure (RealLottoSeed n) :=
  RealUniformInputs.productLaw (RealUniformInputs.law (n - 1)) FourInput.realInputLaw

noncomputable def realSampleArray {n : ℕ} (i : LottoResourceSystem n) (seed : RealLottoSeed n) : FixedArrayTable n ℝ :=
  (i.terminal (i.realPhase seed.1) (i.realPhase_valid seed.1)).realSampleArray seed.2

noncomputable def realSample {n : ℕ} (i : LottoResourceSystem n) (seed : RealLottoSeed n) : Allocation n :=
  (i.realSampleArray seed).read

theorem realSample_fullBudget {n : ℕ} (i : LottoResourceSystem n) (seed : RealLottoSeed n)
    (h : realGroupSeedValid seed.2) : FullBudget i.B (i.realSample seed) :=
  (i.terminal (i.realPhase seed.1) (i.realPhase_valid seed.1)).realSample_fullBudget seed.2 h

theorem realSampleArray_fullBudget {n : ℕ} (i : LottoResourceSystem n) (seed : RealLottoSeed n)
    (h : realGroupSeedValid seed.2) : FullBudget i.B (i.realSampleArray seed).read := i.realSample_fullBudget seed h

noncomputable def realLeafSample {n : ℕ} (i : LottoResourceSystem n) (r : Allocation n) (seed : RealFourSeed) : Allocation n :=
  if hr : i.Valid r then (i.terminal r hr).realSample seed else 0

theorem realLeafSample_measurable {n : ℕ} (i : LottoResourceSystem n) (r : Allocation n) (hr : i.Valid r) :
    Measurable (i.realLeafSample r) := by
  change Measurable (fun seed => if h : i.Valid r then _ else _)
  simp only [dite_eq_left hr]
  exact (i.terminal r hr).realSample_measurable

theorem realLeafSample_law {n : ℕ} (i : LottoResourceSystem n) (r : Allocation n) (hr : i.Valid r) :
    Measure.map (i.realLeafSample r) (FourInput.realInputLaw : Measure RealFourSeed) =
      (i.leafLaw r : Measure (Allocation n)) := by
  change Measure.map (fun seed => if h : i.Valid r then _ else _) _ = _
  simp only [leafLaw, dite_eq_left hr]
  exact (i.terminal r hr).realSample_law

theorem realSample_refines_kernel {n : ℕ} (i : LottoResourceSystem n) (seed : RealLottoSeed n) :
    i.realSample seed = i.tree.realKernel (n - 1) i.initial i.realLeafSample seed := by
  change i.realSample seed = i.realLeafSample (i.tree.realChoice.output (n - 1) i.initial seed.1) seed.2
  rw [← i.realPhase_refines, realLeafSample, dite_eq_left (i.realPhase_valid seed.1)]
  rfl

theorem realSample_measurable {n : ℕ} (i : LottoResourceSystem n) : Measurable i.realSample := by
  have hEq : i.realSample = i.tree.realKernel (n - 1) i.initial i.realLeafSample := funext i.realSample_refines_kernel
  rw [hEq]
  exact i.tree.realKernel_measurable (n - 1) i.initial i.realLeafSample
    (i.tree.forLeaves_mono (fun r hr => i.realLeafSample_measurable r hr) i.tree_valid) i.tree_height

theorem realSample_law {n : ℕ} (i : LottoResourceSystem n) :
    Measure.map i.realSample (realInputLaw n : Measure (RealLottoSeed n)) = (i.law : Measure (Allocation n)) := by
  have hEq : i.realSample = i.tree.realKernel (n - 1) i.initial i.realLeafSample := funext i.realSample_refines_kernel
  rw [hEq]
  exact i.tree.realKernel_law (n - 1) i.initial FourInput.realInputLaw i.realLeafSample i.leafLaw
    (i.tree.forLeaves_mono (fun r hr => i.realLeafSample_measurable r hr) i.tree_valid)
    (i.tree.forLeaves_mono (fun r hr => i.realLeafSample_law r hr) i.tree_valid) i.tree_height

theorem realSample_marginal {n : ℕ} (i : LottoResourceSystem n) (j : Fin n) :
    Measure.map (fun seed => i.realSample seed j) (realInputLaw n : Measure (RealLottoSeed n)) =
      zeroUniformLaw (i.length j) (i.initial j / i.length j) := by
  change Measure.map ((fun x : Allocation n => x j) ∘ i.realSample) _ = _
  rw [← Measure.map_map (measurable_pi_apply j) i.realSample_measurable, i.realSample_law]
  exact i.law_zeroUniform j

end LottoResourceSystem
end Blotto
