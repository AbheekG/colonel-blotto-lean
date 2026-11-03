import Blotto.FareyTemporalSampling
import Blotto.FareyOriginalSourceCompiler

/-! Original rational game data now produce a retained-history strategy
descriptor at half the requested error. Actual finite private seeds draw
rational original-budget rows. Their independent whole laws obey both
continuous Nash regret bounds at the requested error, and bounded preparation
keeps the previous exhaustion guarantee. The exact gate is still semantic;
complete physical encoding, efficient extrema and model prices remain open. -/

namespace Blotto.FareyNativeOutputCompiler
open FareyOriginalSourceCompiler FareyTemporalOutput FareyUnitSourceInputs MeasureTheory
open scoped BigOperators Classical

def trainingAccuracy (epsilon : ℚ) : ℚ := epsilon / 2

theorem trainingAccuracy_guards (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) :
    0 < trainingAccuracy epsilon ∧ trainingAccuracy epsilon ≤ 1 := by
  dsimp [trainingAccuracy]
  constructor <;> linarith [he.1, he.2]

abbrev Output {n : ℕ} (i : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) :=
  Prepared i.ratio i.ratio_guards i.values (trainingAccuracy epsilon) (trainingAccuracy_guards epsilon he)

def preparationSeedCap {n : ℕ} (i : Input (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) : ℕ :=
  sourceSeedCap i.ratio i.ratio_guards i.values (trainingAccuracy epsilon)
    (trainingAccuracy_guards epsilon he) accuracy

noncomputable def prepare {n : ℕ} (i : Input (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) (attempts : ℕ)
    (bits : Fin (attempts * preparationSeedCap i epsilon he accuracy) → Bool) : Option (Output i epsilon he) :=
  FareyTemporalOutput.restart i.ratio i.ratio_guards i.values (trainingAccuracy epsilon)
    (trainingAccuracy_guards epsilon he) accuracy attempts bits

theorem prepare_failure_bound {n : ℕ} (i : Input (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy ∧ accuracy ≤ 1 / 16) (attempts : ℕ) :
    (fairBitKernel (attempts * preparationSeedCap i epsilon he accuracy)).mean
      (fun bits => if prepare i epsilon he accuracy attempts bits = none then 1 else 0) ≤ (1 / 4 : ℝ) ^ attempts :=
  FareyTemporalOutput.restart_failure_bound i.ratio i.ratio_guards i.values (trainingAccuracy epsilon)
    (trainingAccuracy_guards epsilon he) accuracy ha attempts

abbrev richBitCap {n : ℕ} {i : Input (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Output i epsilon he) : ℕ := p.richSeedCap (outputRowError epsilon) (outputTimeAttempts epsilon)

abbrev poorBitCap {n : ℕ} {i : Input (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Output i epsilon he) : ℕ := p.poorSeedCap (outputRowError epsilon) (outputTimeAttempts epsilon)

def richDraw {n : ℕ} {i : Input (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Output i epsilon he) (bits : Fin (richBitCap p) → Bool) : Fin (n + 1) → ℚ :=
  fun field => i.richBudget * p.richSample (outputRowError epsilon) (outputTimeAttempts epsilon) bits field

def poorDraw {n : ℕ} {i : Input (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Output i epsilon he) (bits : Fin (poorBitCap p) → Bool) : Fin (n + 1) → ℚ :=
  fun field => i.richBudget * p.poorSample (outputRowError epsilon) (outputTimeAttempts epsilon) bits field

noncomputable def richLaw {n : ℕ} {i : Input (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Output i epsilon he) : Mixed (n + 1) :=
  (fairBitLaw (richBitCap p)).map (fun bits field => (richDraw p bits field : ℝ))

noncomputable def poorLaw {n : ℕ} {i : Input (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Output i epsilon he) : Mixed (n + 1) :=
  (fairBitLaw (poorBitCap p)).map (fun bits field => (poorDraw p bits field : ℝ))

theorem richLaw_scale {n : ℕ} {i : Input (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Output i epsilon he) :
    richLaw p = scaleLaw (i.richBudget : ℝ) (p.richSampleLaw (outputRowError epsilon) (outputTimeAttempts epsilon)) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun bits field => (richDraw p bits field : ℝ))
    (fairBitLaw (richBitCap p) : Measure (Fin (richBitCap p) → Bool)) =
    Measure.map (scaleAllocation (i.richBudget : ℝ))
      (Measure.map (fun bits field => (p.richSample (outputRowError epsilon) (outputTimeAttempts epsilon) bits field : ℝ))
        (fairBitLaw (richBitCap p) : Measure (Fin (richBitCap p) → Bool)))
  rw [Measure.map_map (measurable_scaleAllocation _) (measurable_of_countable _)]
  congr 1
  funext bits field
  simp only [richDraw, Rat.cast_mul, Function.comp_def, scaleAllocation]

theorem poorLaw_scale {n : ℕ} {i : Input (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Output i epsilon he) :
    poorLaw p = scaleLaw (i.richBudget : ℝ) (p.poorSampleLaw (outputRowError epsilon) (outputTimeAttempts epsilon)) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun bits field => (poorDraw p bits field : ℝ))
    (fairBitLaw (poorBitCap p) : Measure (Fin (poorBitCap p) → Bool)) =
    Measure.map (scaleAllocation (i.richBudget : ℝ))
      (Measure.map (fun bits field => (p.poorSample (outputRowError epsilon) (outputTimeAttempts epsilon) bits field : ℝ))
        (fairBitLaw (poorBitCap p) : Measure (Fin (poorBitCap p) → Bool)))
  rw [Measure.map_map (measurable_scaleAllocation _) (measurable_of_countable _)]
  congr 1
  funext bits field
  simp only [poorDraw, Rat.cast_mul, Function.comp_def, scaleAllocation]

theorem draw_feasible {n : ℕ} {i : Input (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Output i epsilon he) (richBits : Fin (richBitCap p) → Bool) (poorBits : Fin (poorBitCap p) → Bool) :
    Feasible (i.richBudget : ℝ) (fun field => (richDraw p richBits field : ℝ)) ∧
      Feasible (i.poorBudget : ℝ) (fun field => (poorDraw p poorBits field : ℝ)) := by
  have hRows := p.sample_rows_feasible _ (outputRowError_positive epsilon he.1)
    (outputTimeAttempts epsilon) richBits poorBits
  have hBudget : (0 : ℝ) ≤ i.richBudget := by exact_mod_cast i.rich_positive.le
  have hRich := scaleAllocation_feasible hBudget hRows.1
  have hPoor := scaleAllocation_feasible hBudget hRows.2
  rw [mul_one] at hRich
  rw [i.scaled_ratio] at hPoor
  change Feasible (i.richBudget : ℝ) (fun field => (i.richBudget : ℝ) *
    (p.richSample (outputRowError epsilon) (outputTimeAttempts epsilon) richBits field : ℝ)) at hRich
  change Feasible (i.poorBudget : ℝ) (fun field => (i.richBudget : ℝ) *
    (p.poorSample (outputRowError epsilon) (outputTimeAttempts epsilon) poorBits field : ℝ)) at hPoor
  constructor
  · simpa only [richDraw, Rat.cast_mul] using hRich
  · simpa only [poorDraw, Rat.cast_mul] using hPoor

theorem laws_sound {n : ℕ} {i : Input (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Output i epsilon he) :
    Supported (i.richBudget : ℝ) (richLaw p) ∧ Supported (i.poorBudget : ℝ) (poorLaw p) ∧
      regret i.values.values (i.richBudget : ℝ) (richLaw p) (poorLaw p) ≤ (epsilon : ℝ) ∧
        regret i.values.values (i.poorBudget : ℝ) (poorLaw p) (richLaw p) ≤ (epsilon : ℝ) := by
  have hSupported := p.samples_supported _ (outputRowError_positive epsilon he.1) (outputTimeAttempts epsilon)
  have hRegret := p.scheduled_sampled_regrets epsilon he.1 le_rfl
  have hBudget : (0 : ℝ) < i.richBudget := by exact_mod_cast i.rich_positive
  rw [richLaw_scale, poorLaw_scale]
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [mul_one] using scaleLaw_supported hBudget.le _ hSupported.1
  · simpa only [i.scaled_ratio] using scaleLaw_supported hBudget.le _ hSupported.2
  · have h := regret_scale i.values.values hBudget 1
      (p.richSampleLaw (outputRowError epsilon) (outputTimeAttempts epsilon))
      (p.poorSampleLaw (outputRowError epsilon) (outputTimeAttempts epsilon))
    rw [mul_one] at h
    rw [h]
    exact hRegret.1
  · have h := regret_scale i.values.values hBudget (i.ratio : ℝ)
      (p.poorSampleLaw (outputRowError epsilon) (outputTimeAttempts epsilon))
      (p.richSampleLaw (outputRowError epsilon) (outputTimeAttempts epsilon))
    rw [i.scaled_ratio] at h
    rw [h]
    exact hRegret.2

theorem independent_draw_law {n : ℕ} {i : Input (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Output i epsilon he) :
    Measure.map (Prod.map (fun bits field => (richDraw p bits field : ℝ))
      (fun bits field => (poorDraw p bits field : ℝ)))
      ((fairBitLaw (richBitCap p) : Measure (Fin (richBitCap p) → Bool)).prod
        (fairBitLaw (poorBitCap p) : Measure (Fin (poorBitCap p) → Bool))) =
      (richLaw p : Measure (Allocation (n + 1))).prod (poorLaw p : Measure (Allocation (n + 1))) :=
  independent_seed_pair_law _ _ _ _

end Blotto.FareyNativeOutputCompiler
