import Blotto.CompactTemporalSampler
import Blotto.ProductSamplerStability

/-! The actual flat-seed temporal sampler defines a whole-allocation law.
Every draw obeys its hard at-most budget; every measurable event and each
closed marginal CDF differ from the exact temporal law by row tolerance plus
the time rejection tail. This retains all within-player dependence and gives
canonical continuous regret transfer, including every positive/zero tie. -/

namespace Blotto.ProductSecurityTrainer
open MeasureTheory Set Filter
open scoped BigOperators Classical

noncomputable def temporalSampleLaw {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) (A : ℕ) (error : ℚ)
    (timeAttempts : ℕ) : Mixed (n + 1) :=
  (fairBitLaw (c.temporalSeedCap past A error timeAttempts)).map
    (fun bits field => (c.temporalSample cfg past hPast A error timeAttempts bits field : ℝ))

theorem temporalSampleLaw_supported {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) (A : ℕ)
    (error : ℚ) (he : 0 < error) (timeAttempts : ℕ) :
    Supported (c.budgetA : ℝ) (c.temporalSampleLaw cfg past hPast A error timeAttempts) := by
  change ∀ᵐ row ∂Measure.map
    (fun bits field => (c.temporalSample cfg past hPast A error timeAttempts bits field : ℝ))
    (fairBitLaw (c.temporalSeedCap past A error timeAttempts) :
      Measure (Fin (c.temporalSeedCap past A error timeAttempts) → Bool)), Feasible (c.budgetA : ℝ) row
  rw [ae_map_iff (measurable_of_countable _).aemeasurable (ProductBidTree.feasible_measurable _)]
  exact Eventually.of_forall (c.temporalSample_feasible cfg past hPast A error he timeAttempts)

theorem temporalSampleLaw_event {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) (A : ℕ) (error : ℚ)
    (timeAttempts : ℕ) (event : Set (Allocation (n + 1))) (hEvent : MeasurableSet event) :
    (c.temporalSampleLaw cfg past hPast A error timeAttempts : Measure (Allocation (n + 1))).real event =
      (fairBitKernel (c.temporalSeedCap past A error timeAttempts)).mean (fun bits =>
        if (fun field => (c.temporalSample cfg past hPast A error timeAttempts bits field : ℝ)) ∈ event
          then 1 else 0) := by
  change (Measure.map
    (fun bits field => (c.temporalSample cfg past hPast A error timeAttempts bits field : ℝ))
    (fairBitLaw (c.temporalSeedCap past A error timeAttempts) :
      Measure (Fin (c.temporalSeedCap past A error timeAttempts) → Bool))).real event = _
  rw [map_measureReal_apply (measurable_of_countable _) hEvent]
  change _ = ∫ bits, _ ∂(fairBitLaw (c.temporalSeedCap past A error timeAttempts) :
    Measure (Fin (c.temporalSeedCap past A error timeAttempts) → Bool))
  have hIndicator : (fun bits : Fin (c.temporalSeedCap past A error timeAttempts) → Bool =>
      if (fun field => (c.temporalSample cfg past hPast A error timeAttempts bits field : ℝ)) ∈ event
        then (1 : ℝ) else 0) =
      ((fun bits field => (c.temporalSample cfg past hPast A error timeAttempts bits field : ℝ)) ⁻¹' event).indicator
        (fun _ => 1) := by funext bits; rfl
  rw [hIndicator, integral_indicator_const _ (hEvent.preimage (measurable_of_countable _)),
    smul_eq_mul, mul_one]

theorem temporalSampleLaw_event_error {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) (A : ℕ)
    (hA : ∀ field, binaryWordWidth (cfg.capsA field + 1) ≤ A)
    (error : ℚ) (he : 0 < error) (timeAttempts : ℕ)
    (event : Set (Allocation (n + 1))) (hEvent : MeasurableSet event) :
    |(c.temporalSampleLaw cfg past hPast A error timeAttempts : Measure (Allocation (n + 1))).real event -
      ((c.averageLawA past hPast).law : Measure (Allocation (n + 1))).real event| ≤
        (error : ℝ) + 1 / (2 : ℝ) ^ timeAttempts := by
  rw [c.temporalSampleLaw_event cfg past hPast A error timeAttempts event hEvent,
    ← RationalWholeRowLaw.rowKernel_event _ event hEvent]
  exact c.temporalSample_mean_error cfg past hPast A hA error he timeAttempts
    (fun row => if (fun field => (row field : ℝ)) ∈ event then 1 else 0)
    (fun row => by split_ifs <;> norm_num)

theorem temporalSampleLaw_CDFClose {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) (A : ℕ)
    (hA : ∀ field, binaryWordWidth (cfg.capsA field + 1) ≤ A)
    (error : ℚ) (he : 0 < error) (timeAttempts : ℕ) :
    CDFClose (c.temporalSampleLaw cfg past hPast A error timeAttempts) (c.averageLawA past hPast).law
      ((error : ℝ) + 1 / (2 : ℝ) ^ timeAttempts) := by
  intro field threshold
  unfold closedCDF marginal
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [map_measureReal_apply (measurable_pi_apply field) measurableSet_Iic,
    map_measureReal_apply (measurable_pi_apply field) measurableSet_Iic]
  exact c.temporalSampleLaw_event_error cfg past hPast A hA error he timeAttempts
    {row | row field ≤ threshold} (measurableSet_le (measurable_pi_apply field) measurable_const)

end Blotto.ProductSecurityTrainer
