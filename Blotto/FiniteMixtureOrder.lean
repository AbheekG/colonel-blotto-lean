import Blotto.RealCDFDistance

/-! Reordering two independent finite draws preserves the whole law. This is
used only for distributional proofs, not to enumerate support at runtime. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

theorem probabilityMixture_commute {α : Type*} [MeasurableSpace α] {k m : ℕ}
    (a : Fin k → ℝ) (b : Fin m → ℝ) (law : Fin k → Fin m → ProbabilityMeasure α)
    (ha : ∀ i, 0 ≤ a i) (hsa : ∑ i, a i = 1)
    (hb : ∀ j, 0 ≤ b j) (hsb : ∑ j, b j = 1) :
    probabilityMixture a (fun i => probabilityMixture b (law i) hb hsb) ha hsa =
      probabilityMixture b (fun j => probabilityMixture a (fun i => law i j) ha hsa) hb hsb := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro A hA
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (probabilityMixture a (fun i => probabilityMixture b (law i) hb hsb) ha hsa : Measure α).real A =
    (probabilityMixture b (fun j => probabilityMixture a (fun i => law i j) ha hsa) hb hsb : Measure α).real A
  rw [probabilityMixture_real_apply _ _ _ _ _ hA, probabilityMixture_real_apply _ _ _ _ _ hA]
  simp_rw [probabilityMixture_real_apply _ _ _ _ _ hA, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

end Blotto
