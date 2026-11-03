import Blotto.FareyCertifiedTemporalSource
import Blotto.WholeQuantileFareyComparator
import Blotto.UnitSecurityMinimax

/-! Positive acceptance of the actual paired bounded-bit source runs for
positive normalized budgets and any nonempty field set. The continuous
minimax identity and concrete Farey comparator bound imply that two good
native histories pass the exact rational gate. The probability bound uses
the two independent finite fair-bit kernels, not an ideal training history.
Efficient gate access, restart execution and original-game compilation remain
separate; preparation selects laws whose subsequent player draws are independent. -/

namespace Blotto.FareyUnitSourceInputs
open FareySourceTraining ProductSecurityTrainer ContinuousSecurityValues
open scoped BigOperators Classical

theorem good_temporal_pair_gate {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (richPast poorPast : List (RawObservation (n + 1)))
    (hRich : 0 < richPast.length) (hPoor : 0 < poorPast.length)
    (hRichGap : (trainer ratio hr values true epsilon he).rawGap richPast ≤ (epsilon : ℝ) / 8)
    (hPoorGap : (trainer ratio hr values false epsilon he).rawGap poorPast ≤ (epsilon : ℝ) / 8) :
    temporalRationalGate ratio hr values epsilon he richPast poorPast hRich hPoor epsilon = true := by
  have hRichFloor := WholeQuantileFareyComparator.responseFloor_le_lossInfimum_epsilon
    ratio hr values true epsilon he richPast hRich
  have hPoorFloor := WholeQuantileFareyComparator.responseFloor_le_lossInfimum_epsilon
    ratio hr values false epsilon he poorPast hPoor
  have hRF : (trainer ratio hr values true epsilon he).responseFloor richPast ≤
      lossInfimum values.values 1 (ratio : ℝ) + (epsilon : ℝ) / 64 := by
    simpa only [trainer_budgetA, trainer_budgetB, normalizedInput, ite_true,
      Rat.cast_one] using hRichFloor
  have hPF : (trainer ratio hr values false epsilon he).responseFloor poorPast ≤
      lossInfimum values.values (ratio : ℝ) 1 + (epsilon : ℝ) / 64 := by
    simpa only [trainer_budgetA, trainer_budgetB, normalizedInput, Bool.false_eq_true,
      ite_false, Rat.cast_one] using hPoorFloor
  have hValue := UnitSecurityMinimax.lossInfimum_sum_eq_one values.values (ratio : ℝ)
    ⟨by exact_mod_cast hr.1, by exact_mod_cast hr.2⟩
  have hCeil : (trainer ratio hr values true epsilon he).responseCeiling richPast +
      (trainer ratio hr values false epsilon he).responseCeiling poorPast ≤ 1 + (epsilon : ℝ) := by
    rw [responseCeiling_eq_floor_gap, responseCeiling_eq_floor_gap]
    have hE : (0 : ℝ) < epsilon := by exact_mod_cast he.1
    linarith
  exact (temporalRationalGate_true_iff ratio hr values epsilon he richPast poorPast
    hRich hPoor epsilon).mpr
      ((temporal_pair_gate_iff ratio hr values epsilon he richPast poorPast
        hRich hPoor (epsilon : ℝ)).mp hCeil)

theorem good_source_pair_returns {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ)
    (richBits : Fin ((normalizedInput ratio hr values true).rounds epsilon *
      (normalizedInput ratio hr values true).seedCap epsilon he accuracy) → Bool)
    (poorBits : Fin ((normalizedInput ratio hr values false).rounds epsilon *
      (normalizedInput ratio hr values false).seedCap epsilon he accuracy) → Bool)
    (hRich : (trainer ratio hr values true epsilon he).rawGap
      ((normalizedInput ratio hr values true).run epsilon he accuracy richBits) ≤ (epsilon : ℝ) / 8)
    (hPoor : (trainer ratio hr values false epsilon he).rawGap
      ((normalizedInput ratio hr values false).run epsilon he accuracy poorBits) ≤ (epsilon : ℝ) / 8) :
    certifiedSourceRun ratio hr values epsilon he accuracy epsilon richBits poorBits ≠ none := by
  have hGate := good_temporal_pair_gate ratio hr values epsilon he _ _
    (source_run_positive _ epsilon he accuracy richBits)
    (source_run_positive _ epsilon he accuracy poorBits) hRich hPoor
  unfold certifiedSourceRun
  dsimp only
  rw [hGate]
  simp

noncomputable def sourceRejectionMean {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) : ℝ :=
  let richInput := normalizedInput ratio hr values true
  let poorInput := normalizedInput ratio hr values false
  (fairBitKernel (richInput.rounds epsilon * richInput.seedCap epsilon he accuracy)).mean
    (fun richBits =>
      (fairBitKernel (poorInput.rounds epsilon * poorInput.seedCap epsilon he accuracy)).mean
        (fun poorBits => if certifiedSourceRun ratio hr values epsilon he accuracy epsilon
          richBits poorBits = none then 1 else 0))

theorem source_rejection_bound {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) (ha : 0 < accuracy) :
    sourceRejectionMean ratio hr values epsilon he accuracy ≤ 1 / 8 + 2 * (accuracy : ℝ) := by
  let richInput := normalizedInput ratio hr values true
  let poorInput := normalizedInput ratio hr values false
  let richKernel := fairBitKernel (richInput.rounds epsilon * richInput.seedCap epsilon he accuracy)
  let poorKernel := fairBitKernel (poorInput.rounds epsilon * poorInput.seedCap epsilon he accuracy)
  let richBad := fun richBits =>
    if (epsilon : ℝ) / 8 < (trainer ratio hr values true epsilon he).rawGap
      (richInput.run epsilon he accuracy richBits) then (1 : ℝ) else 0
  let poorBad := fun poorBits =>
    if (epsilon : ℝ) / 8 < (trainer ratio hr values false epsilon he).rawGap
      (poorInput.run epsilon he accuracy poorBits) then (1 : ℝ) else 0
  have hPoint : ∀ richBits poorBits,
      (if certifiedSourceRun ratio hr values epsilon he accuracy epsilon richBits poorBits = none
        then (1 : ℝ) else 0) ≤ richBad richBits + poorBad poorBits := by
    intro richBits poorBits
    dsimp only [richBad, poorBad]
    by_cases hRich : (epsilon : ℝ) / 8 < (trainer ratio hr values true epsilon he).rawGap
      (richInput.run epsilon he accuracy richBits)
    · simp only [hRich, ite_true]
      split_ifs <;> norm_num
    · by_cases hPoor : (epsilon : ℝ) / 8 < (trainer ratio hr values false epsilon he).rawGap
        (poorInput.run epsilon he accuracy poorBits)
      · simp only [hRich, hPoor, ite_false, ite_true]
        split_ifs <;> norm_num
      · have hReturn := good_source_pair_returns ratio hr values epsilon he accuracy
          richBits poorBits (le_of_not_gt hRich) (le_of_not_gt hPoor)
        simp only [hReturn, hRich, hPoor, ite_false]
        norm_num
  have hInner : ∀ richBits,
      poorKernel.mean (fun poorBits =>
        if certifiedSourceRun ratio hr values epsilon he accuracy epsilon richBits poorBits = none
          then (1 : ℝ) else 0) ≤ richBad richBits + poorKernel.mean poorBad := by
    intro richBits
    have h := poorKernel.monotone _ _ (hPoint richBits)
    rw [poorKernel.add, poorKernel.constant] at h
    exact h
  have hBoth := richKernel.monotone _ _ hInner
  rw [richKernel.add, richKernel.constant] at hBoth
  have hRich := run_bad_gap_bound richInput epsilon he accuracy ha
  have hPoor := run_bad_gap_bound poorInput epsilon he accuracy ha
  change richKernel.mean richBad ≤ _ at hRich
  change poorKernel.mean poorBad ≤ _ at hPoor
  change sourceRejectionMean ratio hr values epsilon he accuracy ≤ _ at hBoth
  linarith

theorem source_rejection_le_quarter {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy ∧ accuracy ≤ 1 / 16) :
    sourceRejectionMean ratio hr values epsilon he accuracy ≤ 1 / 4 := by
  have h := source_rejection_bound ratio hr values epsilon he accuracy ha.1
  have hAccuracy : (accuracy : ℝ) ≤ 1 / 16 := by
    have hCast : (accuracy : ℝ) ≤ ((1 / 16 : ℚ) : ℝ) := by exact_mod_cast ha.2
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hCast
  linarith

end Blotto.FareyUnitSourceInputs
