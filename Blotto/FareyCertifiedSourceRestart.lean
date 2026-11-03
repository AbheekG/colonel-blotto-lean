import Blotto.FareySourceGateAcceptance
import Blotto.FairBitFirstSuccess

/-! Actual flat finite seeds drive the certified paired source and a bounded
short-circuit restart rule. Returned laws satisfy both original continuous
regret bounds; no exhaustion outcome is silently turned into an equilibrium.
With accuracy at most 1/16, per-trial acceptance is at least 3/4, exhaustion
after k trials is at most 4^(-k), and expected trial visits are at most 4/3.
These seed/visit bounds do not price the source, gate or sampler operations. -/

namespace Blotto.FareyUnitSourceInputs
open FareySourceTraining ProductSecurityTrainer MeasureTheory
open scoped BigOperators Classical

def sourceSeedCap {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) : ℕ :=
  (normalizedInput ratio hr values true).rounds epsilon *
      (normalizedInput ratio hr values true).seedCap epsilon he accuracy +
    (normalizedInput ratio hr values false).rounds epsilon *
      (normalizedInput ratio hr values false).seedCap epsilon he accuracy

noncomputable def certifiedFlatSourceRun {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ)
    (bits : Fin (sourceSeedCap ratio hr values epsilon he accuracy) → Bool) :
    Option (Mixed (n + 1) × Mixed (n + 1)) :=
  let R := (normalizedInput ratio hr values true).rounds epsilon *
    (normalizedInput ratio hr values true).seedCap epsilon he accuracy
  let P := (normalizedInput ratio hr values false).rounds epsilon *
    (normalizedInput ratio hr values false).seedCap epsilon he accuracy
  certifiedSourceRun ratio hr values epsilon he accuracy epsilon
    (firstBitBlock R P bits) (secondBitBlock R P bits)

theorem flat_source_rejection_mean {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) :
    (fairBitKernel (sourceSeedCap ratio hr values epsilon he accuracy)).mean (fun bits =>
      if certifiedFlatSourceRun ratio hr values epsilon he accuracy bits = none then 1 else 0) =
        sourceRejectionMean ratio hr values epsilon he accuracy := by
  exact fairBitKernel_blocks _ _ (fun richBits poorBits =>
    if certifiedSourceRun ratio hr values epsilon he accuracy epsilon richBits poorBits = none then 1 else 0)

theorem flat_source_rejection_le_quarter {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy ∧ accuracy ≤ 1 / 16) :
    (fairBitKernel (sourceSeedCap ratio hr values epsilon he accuracy)).mean (fun bits =>
      if certifiedFlatSourceRun ratio hr values epsilon he accuracy bits = none then 1 else 0) ≤ 1 / 4 := by
  rw [flat_source_rejection_mean]
  exact source_rejection_le_quarter ratio hr values epsilon he accuracy ha

theorem flat_source_acceptance_ge_three_quarters {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy ∧ accuracy ≤ 1 / 16) :
    3 / 4 ≤ (fairBitKernel (sourceSeedCap ratio hr values epsilon he accuracy)).mean (fun bits =>
      if certifiedFlatSourceRun ratio hr values epsilon he accuracy bits = none then 0 else 1) := by
  let k := fairBitKernel (sourceSeedCap ratio hr values epsilon he accuracy)
  let trial := certifiedFlatSourceRun ratio hr values epsilon he accuracy
  have hPartition : k.mean (fun bits => if trial bits = none then 0 else 1) +
      k.mean (fun bits => if trial bits = none then 1 else 0) = 1 := by
    rw [← k.add]
    have hPoint : (fun bits => (if trial bits = none then (0 : ℝ) else 1) +
        (if trial bits = none then 1 else 0)) = fun _ => (1 : ℝ) := by
      funext bits
      split_ifs <;> norm_num
    rw [hPoint, k.constant]
  have hReject := flat_source_rejection_le_quarter ratio hr values epsilon he accuracy ha
  change k.mean (fun bits => if trial bits = none then 1 else 0) ≤ _ at hReject
  change _ ≤ k.mean (fun bits => if trial bits = none then 0 else 1)
  linarith

theorem certifiedFlatSourceRun_sound {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ)
    (bits : Fin (sourceSeedCap ratio hr values epsilon he accuracy) → Bool)
    (richLaw poorLaw : Mixed (n + 1))
    (hResult : certifiedFlatSourceRun ratio hr values epsilon he accuracy bits = some (richLaw, poorLaw)) :
    Supported 1 richLaw ∧ Supported (ratio : ℝ) poorLaw ∧
      regret values.values 1 richLaw poorLaw ≤ (epsilon : ℝ) ∧
        regret values.values (ratio : ℝ) poorLaw richLaw ≤ (epsilon : ℝ) :=
  certifiedSourceRun_sound ratio hr values epsilon he accuracy epsilon _ _ richLaw poorLaw hResult

noncomputable def certifiedSourceRestart {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) (attempts : ℕ)
    (bits : Fin (attempts * sourceSeedCap ratio hr values epsilon he accuracy) → Bool) :
    Option (Mixed (n + 1) × Mixed (n + 1)) :=
  FairBitFirstSuccess.run (sourceSeedCap ratio hr values epsilon he accuracy)
    (certifiedFlatSourceRun ratio hr values epsilon he accuracy) attempts bits

noncomputable def sourceRestartVisits {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) (attempts : ℕ)
    (bits : Fin (attempts * sourceSeedCap ratio hr values epsilon he accuracy) → Bool) : ℕ :=
  FairBitFirstSuccess.visits (sourceSeedCap ratio hr values epsilon he accuracy)
    (certifiedFlatSourceRun ratio hr values epsilon he accuracy) attempts bits

theorem source_restart_sound {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) (attempts : ℕ)
    (bits : Fin (attempts * sourceSeedCap ratio hr values epsilon he accuracy) → Bool)
    (richLaw poorLaw : Mixed (n + 1))
    (hResult : certifiedSourceRestart ratio hr values epsilon he accuracy attempts bits =
      some (richLaw, poorLaw)) :
    Supported 1 richLaw ∧ Supported (ratio : ℝ) poorLaw ∧
      regret values.values 1 richLaw poorLaw ≤ (epsilon : ℝ) ∧
        regret values.values (ratio : ℝ) poorLaw richLaw ≤ (epsilon : ℝ) := by
  apply FairBitFirstSuccess.run_sound _ _ (fun pair =>
    Supported 1 pair.1 ∧ Supported (ratio : ℝ) pair.2 ∧
      regret values.values 1 pair.1 pair.2 ≤ (epsilon : ℝ) ∧
        regret values.values (ratio : ℝ) pair.2 pair.1 ≤ (epsilon : ℝ)) _ attempts bits
      (richLaw, poorLaw) hResult
  intro trialBits pair hPair
  exact certifiedFlatSourceRun_sound ratio hr values epsilon he accuracy trialBits pair.1 pair.2 hPair

theorem source_restart_failure_bound {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy ∧ accuracy ≤ 1 / 16) (attempts : ℕ) :
    (fairBitKernel (attempts * sourceSeedCap ratio hr values epsilon he accuracy)).mean (fun bits =>
      if certifiedSourceRestart ratio hr values epsilon he accuracy attempts bits = none then 1 else 0) ≤
        (1 / 4 : ℝ) ^ attempts :=
  FairBitFirstSuccess.failure_le_quarter_pow _ _
    (flat_source_rejection_le_quarter ratio hr values epsilon he accuracy ha) attempts

theorem source_restart_visits_le_cap {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) (attempts : ℕ)
    (bits : Fin (attempts * sourceSeedCap ratio hr values epsilon he accuracy) → Bool) :
    sourceRestartVisits ratio hr values epsilon he accuracy attempts bits ≤ attempts :=
  FairBitFirstSuccess.visits_le_cap _ _ attempts bits

theorem source_restart_expected_visits {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy ∧ accuracy ≤ 1 / 16) (attempts : ℕ) :
    (fairBitKernel (attempts * sourceSeedCap ratio hr values epsilon he accuracy)).mean (fun bits =>
      (sourceRestartVisits ratio hr values epsilon he accuracy attempts bits : ℝ)) ≤ 4 / 3 :=
  FairBitFirstSuccess.visits_mean_le_four_thirds _ _
    (flat_source_rejection_le_quarter ratio hr values epsilon he accuracy ha) attempts

end Blotto.FareyUnitSourceInputs
