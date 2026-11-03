import Blotto.RationalMachineLaw
import Blotto.WordMachineChoice
import Blotto.RationalAffineAllocation
import Blotto.RationalSegmentMachine

/-! Exact ideal-law identities for native affine output mapping, a binary
root choice, and a categorical segment controller at a fixed scalar block. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators Classical

theorem WordStateMachine.rationalIdealLaw_mapped {S : Type*} {n m : ℕ} (controller : WordStateMachine S (Fin n → ℚ))
    (f : RationalAffineAllocation n m) (s : S) :
    (controller.mapped f.value).rationalIdealLaw s = (controller.rationalIdealLaw s).map f.real.value := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro A hA
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((controller.mapped f.value).rationalIdealLaw s : Measure (Allocation m)).real A =
    (Measure.map f.real.value (controller.rationalIdealLaw s : Measure (Allocation n))).real A
  rw [WordStateMachine.rationalIdealLaw_event _ _ A hA, WordStateMachine.mapped_mean,
    map_measureReal_apply f.real.measurable hA,
    controller.rationalIdealLaw_event s _ (hA.preimage f.real.measurable)]
  congr 1
  funext x
  rw [f.value_real]
  rfl

theorem binaryMachine_rationalIdealLaw {S T : Type*} {n : ℕ} (w : ProbabilityWords)
    (a : WordStateMachine S (Fin n → ℚ)) (b : WordStateMachine T (Fin n → ℚ)) (sa : S) (sb : T) :
    (binaryMachine w a b sa sb).rationalIdealLaw .start = binaryLaw (w.rational : ℝ)
      (by
        have hbQ : (0 : ℚ) < w.denominator := by exact_mod_cast w.denominator_pos
        have hpQ : 0 ≤ w.rational ∧ w.rational ≤ 1 :=
          ⟨by unfold ProbabilityWords.rational; positivity, (div_le_one hbQ).mpr (by exact_mod_cast w.normalized)⟩
        exact_mod_cast hpQ)
      (a.rationalIdealLaw sa) (b.rationalIdealLaw sb) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro A hA
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((binaryMachine w a b sa sb).rationalIdealLaw .start : Measure (Allocation n)).real A =
    (binaryLaw (w.rational : ℝ) _ (a.rationalIdealLaw sa) (b.rationalIdealLaw sb) : Measure (Allocation n)).real A
  rw [WordStateMachine.rationalIdealLaw_event _ _ A hA, binaryMachine_mean]
  unfold binaryLaw
  rw [probabilityMixture_real_apply _ _ _ _ _ hA]
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.univ_unique, Finset.sum_singleton]
  change (w.rational : ℝ) * _ + (1 - (w.rational : ℝ)) * _ =
    (w.rational : ℝ) * (a.rationalIdealLaw sa : Measure (Allocation n)).real A +
      (1 - (w.rational : ℝ)) * (b.rationalIdealLaw sb : Measure (Allocation n)).real A
  rw [a.rationalIdealLaw_event sa A hA, b.rationalIdealLaw_event sb A hA]

theorem RationalSegmentLottery.machine_rationalIdealLaw {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k)
    (K : ℕ) (scalarBits : Fin K → Bool) :
    (l.machine fallback K scalarBits).rationalIdealLaw l.start = l.fixedIdeal K scalarBits := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro A hA
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((l.machine fallback K scalarBits).rationalIdealLaw l.start : Measure (Allocation n)).real A =
    (l.fixedIdeal K scalarBits : Measure (Allocation n)).real A
  rw [WordStateMachine.rationalIdealLaw_event _ _ A hA, l.machine_mean, l.fixedIdeal_event K scalarBits A hA]

end Blotto
