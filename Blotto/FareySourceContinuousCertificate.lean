import Blotto.FareyUnitSourceInputs
import Blotto.ProductSecurityHistoryLaws

/-! The constructed unit Farey source now derives its continuous response
certificate from the actual temporal trainer laws. This removes the supplied
finite response bound from the source-to-continuous join. The ceiling and floor
are semantic finite extrema; efficient extrema access, the continuous minimax
comparator and the original-game compiler remain separate obligations. -/

namespace Blotto.FareyUnitSourceInputs
open FareySourceTraining ProductSecurityTrainer
open scoped BigOperators Classical

theorem temporal_response_bound {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) :
    let c := trainer ratio hr values candidateRich epsilon he
    ∀ y : Allocation (n + 1), Feasible (c.budgetB : ℝ) y →
      purePayoff values.values y (c.averageLawA past hPast).law ≤ c.responseCeiling past := by
  dsimp only
  let c := trainer ratio hr values candidateRich epsilon he
  apply finite_response_bound_continuous ratio hr values candidateRich epsilon he
    (c.averageLawA past hPast) c.codeA (fun _ _ => rfl) (c.responseCeiling past)
  intro code hCode
  exact c.averageLawA_finite_response_bound past hPast code hCode

theorem temporal_response_bound_floor_gap {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) :
    let c := trainer ratio hr values candidateRich epsilon he
    ∀ y : Allocation (n + 1), Feasible (c.budgetB : ℝ) y →
      purePayoff values.values y (c.averageLawA past hPast).law ≤
        c.responseFloor past + c.rawGap past := by
  dsimp only
  intro y hy
  have h := temporal_response_bound ratio hr values candidateRich epsilon he past hPast y hy
  rw [responseCeiling_eq_floor_gap] at h
  exact h

theorem good_temporal_response_bound {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length)
    (hGood : (trainer ratio hr values candidateRich epsilon he).rawGap past ≤ (epsilon : ℝ) / 8) :
    let c := trainer ratio hr values candidateRich epsilon he
    ∀ y : Allocation (n + 1), Feasible (c.budgetB : ℝ) y →
      purePayoff values.values y (c.averageLawA past hPast).law ≤
        c.responseFloor past + (epsilon : ℝ) / 8 := by
  dsimp only
  intro y hy
  exact (temporal_response_bound_floor_gap ratio hr values candidateRich epsilon he past hPast y hy).trans
    (add_le_add (le_refl _) hGood)

theorem rich_temporal_supported {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) :
    Supported 1 ((trainer ratio hr values true epsilon he).averageLawA past hPast).law := by
  have h := (trainer ratio hr values true epsilon he).averageLawA_supported past hPast
  change Supported ((1 : ℚ) : ℝ) _ at h
  simpa only [Rat.cast_one] using h

theorem poor_temporal_supported {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) :
    Supported (ratio : ℝ) ((trainer ratio hr values false epsilon he).averageLawA past hPast).law :=
  (trainer ratio hr values false epsilon he).averageLawA_supported past hPast

theorem source_run_length {n : ℕ} (input : Input (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ)
    (bits : Fin (input.rounds epsilon * input.seedCap epsilon he accuracy) → Bool) :
    (input.run epsilon he accuracy bits).length = input.rounds epsilon := by
  unfold Input.seedCap at bits
  unfold Input.run ProductSecurityTrainer.compactScheduledRun
    ProductSecurityTrainer.compactNativeRun NativeImplicitTrainingHistory.run
  rw [runBitHistory_length]
  simp only [List.length_nil, Nat.add_zero]

theorem source_run_positive {n : ℕ} (input : Input (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ)
    (bits : Fin (input.rounds epsilon * input.seedCap epsilon he accuracy) → Bool) :
    0 < (input.run epsilon he accuracy bits).length := by
  rw [source_run_length]
  exact trainingRounds_positive _ _ _

/-- On the actual bounded-bit run, failure of the continuous floor-plus-gap
certificate is a subset of the already controlled bad training-gap event.
The candidate law contains whole original code rows and has a hard budget. -/
theorem source_run_continuous_failure_bound {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy) :
    let input := normalizedInput ratio hr values candidateRich
    let c := trainer ratio hr values candidateRich epsilon he
    (fairBitKernel (input.rounds epsilon * input.seedCap epsilon he accuracy)).mean (fun bits =>
      let past := input.run epsilon he accuracy bits
      if ∃ y : Allocation (n + 1), Feasible (c.budgetB : ℝ) y ∧
          c.responseFloor past + (epsilon : ℝ) / 8 <
            purePayoff values.values y (c.averageLawA past
              (source_run_positive input epsilon he accuracy bits)).law
      then 1 else 0) ≤ 1 / 16 + (accuracy : ℝ) := by
  dsimp only
  let input := normalizedInput ratio hr values candidateRich
  let c := trainer ratio hr values candidateRich epsilon he
  have hPoint : ∀ bits : Fin (input.rounds epsilon * input.seedCap epsilon he accuracy) → Bool,
      (if ∃ y : Allocation (n + 1), Feasible (c.budgetB : ℝ) y ∧
          c.responseFloor (input.run epsilon he accuracy bits) + (epsilon : ℝ) / 8 <
            purePayoff values.values y (c.averageLawA (input.run epsilon he accuracy bits)
              (source_run_positive input epsilon he accuracy bits)).law then (1 : ℝ) else 0) ≤
        (if (epsilon : ℝ) / 8 < c.rawGap (input.run epsilon he accuracy bits) then 1 else 0) := by
    intro bits
    split_ifs with hViolation hGap
    · exact le_rfl
    · obtain ⟨y, hy, hPayoff⟩ := hViolation
      have hGood := good_temporal_response_bound ratio hr values candidateRich epsilon he
        (input.run epsilon he accuracy bits) (source_run_positive input epsilon he accuracy bits)
        (le_of_not_gt hGap) y hy
      exact False.elim (not_lt_of_ge hGood hPayoff)
    · norm_num
    · exact le_rfl
  exact ((fairBitKernel _).monotone _ _ hPoint).trans
    (run_bad_gap_bound input epsilon he accuracy ha)

end Blotto.FareyUnitSourceInputs
