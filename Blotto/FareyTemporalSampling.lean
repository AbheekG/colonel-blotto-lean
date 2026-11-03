import Blotto.FareyTemporalOutput
import Blotto.IndependentWholeSamplers

/-! An accepted history descriptor drives actual native rich/poor temporal
whole-row draws. Source code-width guards are derived from the normalized
Farey inputs. Private bit seeds give independent player laws; their continuous
regrets include both row errors and bounded time-choice tails. A concrete
tolerance/precision schedule reserves half the final error for sampling.
No efficient gate, physical encoding or complete sampling runtime is claimed. -/

namespace Blotto.FareyTemporalOutput
open FareyUnitSourceInputs FareySourceTraining ProductSecurityTrainer MeasureTheory
open scoped BigOperators Classical

def Prepared.richSeedCap {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) (error : ℚ) (timeAttempts : ℕ) : ℕ :=
  (trainer ratio hr values true epsilon he).temporalSeedCap p.richPast
    ((normalizedInput ratio hr values true).width epsilon) error timeAttempts

def Prepared.poorSeedCap {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) (error : ℚ) (timeAttempts : ℕ) : ℕ :=
  (trainer ratio hr values false epsilon he).temporalSeedCap p.poorPast
    ((normalizedInput ratio hr values false).width epsilon) error timeAttempts

theorem Prepared.richSeedCap_source {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) (error : ℚ) (timeAttempts : ℕ) :
    p.richSeedCap error timeAttempts =
      timeAttempts * UniformNatRejection.width ((normalizedInput ratio hr values true).rounds epsilon) +
        compactLeafSeedCap n ((normalizedInput ratio hr values true).rounds epsilon)
          ((normalizedInput ratio hr values true).width epsilon) error := by
  unfold Prepared.richSeedCap temporalSeedCap temporalRowSeedCap
  rw [p.rich_length]

theorem Prepared.poorSeedCap_source {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) (error : ℚ) (timeAttempts : ℕ) :
    p.poorSeedCap error timeAttempts =
      timeAttempts * UniformNatRejection.width ((normalizedInput ratio hr values false).rounds epsilon) +
        compactLeafSeedCap n ((normalizedInput ratio hr values false).rounds epsilon)
          ((normalizedInput ratio hr values false).width epsilon) error := by
  unfold Prepared.poorSeedCap temporalSeedCap temporalRowSeedCap
  rw [p.poor_length]

def Prepared.richSample {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) (error : ℚ) (timeAttempts : ℕ)
    (bits : Fin (p.richSeedCap error timeAttempts) → Bool) : Fin (n + 1) → ℚ :=
  (trainer ratio hr values true epsilon he).temporalSample
    ((normalizedInput ratio hr values true).config epsilon he) p.richPast p.rich_positive
    ((normalizedInput ratio hr values true).width epsilon) error timeAttempts bits

def Prepared.poorSample {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) (error : ℚ) (timeAttempts : ℕ)
    (bits : Fin (p.poorSeedCap error timeAttempts) → Bool) : Fin (n + 1) → ℚ :=
  (trainer ratio hr values false epsilon he).temporalSample
    ((normalizedInput ratio hr values false).config epsilon he) p.poorPast p.poor_positive
    ((normalizedInput ratio hr values false).width epsilon) error timeAttempts bits

noncomputable def Prepared.richSampleLaw {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) (error : ℚ) (timeAttempts : ℕ) : Mixed (n + 1) :=
  (trainer ratio hr values true epsilon he).temporalSampleLaw
    ((normalizedInput ratio hr values true).config epsilon he) p.richPast p.rich_positive
    ((normalizedInput ratio hr values true).width epsilon) error timeAttempts

noncomputable def Prepared.poorSampleLaw {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) (error : ℚ) (timeAttempts : ℕ) : Mixed (n + 1) :=
  (trainer ratio hr values false epsilon he).temporalSampleLaw
    ((normalizedInput ratio hr values false).config epsilon he) p.poorPast p.poor_positive
    ((normalizedInput ratio hr values false).width epsilon) error timeAttempts

theorem Prepared.sample_rows_feasible {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) (error : ℚ) (hError : 0 < error) (timeAttempts : ℕ)
    (richBits : Fin (p.richSeedCap error timeAttempts) → Bool)
    (poorBits : Fin (p.poorSeedCap error timeAttempts) → Bool) :
    Feasible 1 (fun field => (p.richSample error timeAttempts richBits field : ℝ)) ∧
      Feasible (ratio : ℝ) (fun field => (p.poorSample error timeAttempts poorBits field : ℝ)) := by
  constructor
  · have h := (trainer ratio hr values true epsilon he).temporalSample_feasible
      ((normalizedInput ratio hr values true).config epsilon he) p.richPast p.rich_positive
      ((normalizedInput ratio hr values true).width epsilon) error hError timeAttempts richBits
    change Feasible ((1 : ℚ) : ℝ) (fun field => (p.richSample error timeAttempts richBits field : ℝ)) at h
    simpa only [Rat.cast_one] using h
  · exact (trainer ratio hr values false epsilon he).temporalSample_feasible
      ((normalizedInput ratio hr values false).config epsilon he) p.poorPast p.poor_positive
      ((normalizedInput ratio hr values false).width epsilon) error hError timeAttempts poorBits

theorem Prepared.samples_supported {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) (error : ℚ) (hError : 0 < error) (timeAttempts : ℕ) :
    Supported 1 (p.richSampleLaw error timeAttempts) ∧
      Supported (ratio : ℝ) (p.poorSampleLaw error timeAttempts) := by
  constructor
  · have h := (trainer ratio hr values true epsilon he).temporalSampleLaw_supported
        ((normalizedInput ratio hr values true).config epsilon he) p.richPast p.rich_positive
        ((normalizedInput ratio hr values true).width epsilon) error hError timeAttempts
    change Supported ((1 : ℚ) : ℝ) (p.richSampleLaw error timeAttempts) at h
    simpa only [Rat.cast_one] using h
  · exact (trainer ratio hr values false epsilon he).temporalSampleLaw_supported
      ((normalizedInput ratio hr values false).config epsilon he) p.poorPast p.poor_positive
      ((normalizedInput ratio hr values false).width epsilon) error hError timeAttempts

theorem Prepared.richSample_CDFClose {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) (error : ℚ) (hError : 0 < error) (timeAttempts : ℕ) :
    CDFClose (p.richSampleLaw error timeAttempts) p.laws.1
      ((error : ℝ) + 1 / (2 : ℝ) ^ timeAttempts) :=
  (trainer ratio hr values true epsilon he).temporalSampleLaw_CDFClose
    ((normalizedInput ratio hr values true).config epsilon he) p.richPast p.rich_positive
    ((normalizedInput ratio hr values true).width epsilon)
    (source_widths (normalizedInput ratio hr values true) epsilon).1 error hError timeAttempts

theorem Prepared.poorSample_CDFClose {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) (error : ℚ) (hError : 0 < error) (timeAttempts : ℕ) :
    CDFClose (p.poorSampleLaw error timeAttempts) p.laws.2
      ((error : ℝ) + 1 / (2 : ℝ) ^ timeAttempts) :=
  (trainer ratio hr values false epsilon he).temporalSampleLaw_CDFClose
    ((normalizedInput ratio hr values false).config epsilon he) p.poorPast p.poor_positive
    ((normalizedInput ratio hr values false).width epsilon)
    (source_widths (normalizedInput ratio hr values false) epsilon).1 error hError timeAttempts

theorem Prepared.sampled_regrets {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) (error : ℚ) (hError : 0 < error) (timeAttempts : ℕ) :
    regret values.values 1 (p.richSampleLaw error timeAttempts) (p.poorSampleLaw error timeAttempts) ≤
        (epsilon : ℝ) + 3 * ((error : ℝ) + 1 / (2 : ℝ) ^ timeAttempts) ∧
      regret values.values (ratio : ℝ) (p.poorSampleLaw error timeAttempts) (p.richSampleLaw error timeAttempts) ≤
        (epsilon : ℝ) + 3 * ((error : ℝ) + 1 / (2 : ℝ) ^ timeAttempts) := by
  have hTarget := p.laws_sound
  have hSamples := productSampler_regret_stability values.values values.values (A := 1) (B := (ratio : ℝ)) (by norm_num)
    (by exact_mod_cast hr.1.le) p.laws.1 p.laws.2 (p.richSampleLaw error timeAttempts)
    (p.poorSampleLaw error timeAttempts) (p.richSample_CDFClose error hError timeAttempts)
    (p.poorSample_CDFClose error hError timeAttempts)
  constructor <;> linarith [hTarget.2.2.1, hTarget.2.2.2, hSamples.1, hSamples.2]

theorem Prepared.independent_sample_law {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) (error : ℚ) (timeAttempts : ℕ) :
    Measure.map (Prod.map (fun bits field => (p.richSample error timeAttempts bits field : ℝ))
      (fun bits field => (p.poorSample error timeAttempts bits field : ℝ)))
      ((fairBitLaw (p.richSeedCap error timeAttempts) : Measure (Fin (p.richSeedCap error timeAttempts) → Bool)).prod
        (fairBitLaw (p.poorSeedCap error timeAttempts) : Measure (Fin (p.poorSeedCap error timeAttempts) → Bool))) =
      (p.richSampleLaw error timeAttempts : Measure (Allocation (n + 1))).prod
        (p.poorSampleLaw error timeAttempts : Measure (Allocation (n + 1))) :=
  independent_seed_pair_law _ _ _ _

def outputRowError (tolerance : ℚ) : ℚ := tolerance / 12

def outputTimeAttempts (tolerance : ℚ) : ℕ :=
  RationalWeightedGuideTree.epsilonPrecision (outputRowError tolerance)

theorem outputRowError_positive (tolerance : ℚ) (hTolerance : 0 < tolerance) :
    0 < outputRowError tolerance := div_pos hTolerance (by norm_num)

theorem output_time_tail (tolerance : ℚ) (hTolerance : 0 < tolerance) :
    1 / (2 : ℝ) ^ outputTimeAttempts tolerance ≤ (outputRowError tolerance : ℝ) :=
  RationalWeightedGuideTree.epsilonPrecision_guard _ (outputRowError_positive tolerance hTolerance)

theorem Prepared.scheduled_sampled_regrets {n : ℕ} {ratio : ℚ} {hr : 0 < ratio ∧ ratio ≤ 1}
    {values : RationalFieldSelector (n + 1)} {epsilon : ℚ} {he : 0 < epsilon ∧ epsilon ≤ 1}
    (p : Prepared ratio hr values epsilon he) (tolerance : ℚ) (hTolerance : 0 < tolerance)
    (hReserve : epsilon ≤ tolerance / 2) :
    regret values.values 1 (p.richSampleLaw (outputRowError tolerance) (outputTimeAttempts tolerance))
        (p.poorSampleLaw (outputRowError tolerance) (outputTimeAttempts tolerance)) ≤ (tolerance : ℝ) ∧
      regret values.values (ratio : ℝ) (p.poorSampleLaw (outputRowError tolerance) (outputTimeAttempts tolerance))
        (p.richSampleLaw (outputRowError tolerance) (outputTimeAttempts tolerance)) ≤ (tolerance : ℝ) := by
  have h := p.sampled_regrets _ (outputRowError_positive tolerance hTolerance) (outputTimeAttempts tolerance)
  have hTail := output_time_tail tolerance hTolerance
  have hCast : (epsilon : ℝ) ≤ ((tolerance / 2 : ℚ) : ℝ) := by exact_mod_cast hReserve
  have hRow : (outputRowError tolerance : ℝ) = (tolerance : ℝ) / 12 := by
    simp only [outputRowError, Rat.cast_div, Rat.cast_ofNat]
  rw [Rat.cast_div, Rat.cast_ofNat] at hCast
  rw [hRow] at h hTail
  constructor <;> linarith [h.1, h.2]

end Blotto.FareyTemporalOutput
