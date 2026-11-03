import Blotto.FareySourceContinuousCertificate

/-! The actual temporal candidate law has an attained continuous response
supremum, equal to the trainer's finite response ceiling. Both orientations
therefore have an exact security-sum gate for their independent whole laws.
This is a semantic gate: efficient extrema access and a proof that training
passes it still require the finite comparator/minimax and compiler chains. -/

namespace Blotto.FareyUnitSourceInputs
open FareySourceTraining ProductSecurityTrainer
open scoped BigOperators Classical

theorem temporal_security_exact {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) :
    let c := trainer ratio hr values candidateRich epsilon he
    security values.values (c.budgetB : ℝ) (c.averageLawA past hPast).law =
      c.responseCeiling past := by
  dsimp only
  let c := trainer ratio hr values candidateRich epsilon he
  apply le_antisymm
  · apply security_le values.values
      (by exact_mod_cast (normalizedInput ratio hr values candidateRich).budgetB_positive.le)
    exact temporal_response_bound ratio hr values candidateRich epsilon he past hPast
  · let label := FiniteSaddle.maximizingColumn c.actionsB_positive c.matrix
      (rawHistoryAverage (fun h => (c.rawLawA h).realWeight) past)
    have hFeasible := c.averageLawB_row_feasible past hPast label
    have hPayoff := c.averageLawA_response_payoff past hPast label
    change Feasible (c.budgetB : ℝ)
      (fun j => (c.bidsB j (c.codeB label j) : ℝ)) at hFeasible
    have hUpper := purePayoff_le_security values.values hFeasible
      (c.averageLawA past hPast).law
    change purePayoff c.values.values
      (fun j => (c.bidsB j (c.codeB label j) : ℝ))
      (c.averageLawA past hPast).law = _ at hPayoff
    have hValues : c.values = values := trainer_values ratio hr values candidateRich epsilon he
    rw [hValues] at hPayoff
    rw [hPayoff] at hUpper
    exact hUpper

theorem temporal_response_attained {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) :
    let c := trainer ratio hr values candidateRich epsilon he
    ∃ y : Allocation (n + 1), Feasible (c.budgetB : ℝ) y ∧
      purePayoff values.values y (c.averageLawA past hPast).law =
        security values.values (c.budgetB : ℝ) (c.averageLawA past hPast).law := by
  dsimp only
  let c := trainer ratio hr values candidateRich epsilon he
  let label := FiniteSaddle.maximizingColumn c.actionsB_positive c.matrix
    (rawHistoryAverage (fun h => (c.rawLawA h).realWeight) past)
  refine ⟨fun j => (c.bidsB j (c.codeB label j) : ℝ),
    c.averageLawB_row_feasible past hPast label, ?_⟩
  rw [temporal_security_exact]
  exact c.averageLawA_response_payoff past hPast label

theorem rich_temporal_security {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) :
    security values.values (ratio : ℝ)
      ((trainer ratio hr values true epsilon he).averageLawA past hPast).law =
        (trainer ratio hr values true epsilon he).responseCeiling past :=
  temporal_security_exact ratio hr values true epsilon he past hPast

theorem poor_temporal_security {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) :
    security values.values 1
      ((trainer ratio hr values false epsilon he).averageLawA past hPast).law =
        (trainer ratio hr values false epsilon he).responseCeiling past := by
  simpa only [trainer_budgetB, normalizedInput, Bool.false_eq_true, ite_false,
    Rat.cast_one] using temporal_security_exact ratio hr values false epsilon he past hPast

theorem temporal_pair_regret_sum {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (richPast poorPast : List (RawObservation (n + 1)))
    (hRich : 0 < richPast.length) (hPoor : 0 < poorPast.length) :
    let rich := trainer ratio hr values true epsilon he
    let poor := trainer ratio hr values false epsilon he
    let richLaw := (rich.averageLawA richPast hRich).law
    let poorLaw := (poor.averageLawA poorPast hPoor).law
    regret values.values 1 richLaw poorLaw +
      regret values.values (ratio : ℝ) poorLaw richLaw =
        rich.responseCeiling richPast + poor.responseCeiling poorPast - 1 := by
  dsimp only
  rw [regret_sum, rich_temporal_security, poor_temporal_security]
  ring

theorem temporal_pair_gate_iff {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (richPast poorPast : List (RawObservation (n + 1)))
    (hRich : 0 < richPast.length) (hPoor : 0 < poorPast.length) (tolerance : ℝ) :
    let rich := trainer ratio hr values true epsilon he
    let poor := trainer ratio hr values false epsilon he
    let richLaw := (rich.averageLawA richPast hRich).law
    let poorLaw := (poor.averageLawA poorPast hPoor).law
    rich.responseCeiling richPast + poor.responseCeiling poorPast ≤ 1 + tolerance ↔
      regret values.values 1 richLaw poorLaw +
        regret values.values (ratio : ℝ) poorLaw richLaw ≤ tolerance := by
  dsimp only
  rw [temporal_pair_regret_sum]
  constructor <;> intro h <;> linarith

theorem temporal_pair_gate_sound {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (richPast poorPast : List (RawObservation (n + 1)))
    (hRich : 0 < richPast.length) (hPoor : 0 < poorPast.length) (tolerance : ℝ)
    (hGate : (trainer ratio hr values true epsilon he).responseCeiling richPast +
      (trainer ratio hr values false epsilon he).responseCeiling poorPast ≤ 1 + tolerance) :
    let richLaw := ((trainer ratio hr values true epsilon he).averageLawA richPast hRich).law
    let poorLaw := ((trainer ratio hr values false epsilon he).averageLawA poorPast hPoor).law
    regret values.values 1 richLaw poorLaw ≤ tolerance ∧
      regret values.values (ratio : ℝ) poorLaw richLaw ≤ tolerance := by
  dsimp only
  apply regrets_le_of_security_sum values.values _ _
    (rich_temporal_supported ratio hr values epsilon he richPast hRich)
    (poor_temporal_supported ratio hr values epsilon he poorPast hPoor)
  rw [rich_temporal_security, poor_temporal_security]
  linarith

end Blotto.FareyUnitSourceInputs
