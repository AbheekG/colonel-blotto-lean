import Blotto.FareyTemporalSecurityExact
import Blotto.RationalWholeRowPayoff

/-! A finite rational maximum and Boolean sum gate exactly certify the actual
temporal source laws against every continuous deviation. The trainer's label
enumeration and temporal weights are semantic here: this does not supply the
efficient implicit extrema oracle, minimax comparator, successful-trial bound,
or original-budget compiler needed by the complete FPTAS. -/

namespace Blotto
open scoped BigOperators Classical

def finiteRationalMaximum {r : ℕ} (hr : 0 < r) (score : Fin r → ℚ) : ℚ :=
  Finset.univ.sup' ⟨⟨0, hr⟩, Finset.mem_univ _⟩ score

theorem finiteRationalMaximum_attained {r : ℕ} (hr : 0 < r) (score : Fin r → ℚ) :
    ∃ i, finiteRationalMaximum hr score = score i := by
  obtain ⟨i, _hi, h⟩ := Finset.exists_mem_eq_sup'
    (⟨⟨0, hr⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin r)).Nonempty) score
  exact ⟨i, h⟩

theorem le_finiteRationalMaximum {r : ℕ} (hr : 0 < r) (score : Fin r → ℚ) (i : Fin r) :
    score i ≤ finiteRationalMaximum hr score :=
  Finset.le_sup' score (Finset.mem_univ i)

namespace ProductSecurityTrainer

noncomputable def rationalResponseScore {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length) (j : Fin c.actionsB) : ℚ :=
  (c.averageLawA past hPast).rationalPurePayoff c.values
    (fun field => c.bidsB field (c.codeB j field))

theorem rationalResponseScore_cast {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length) (j : Fin c.actionsB) :
    (c.rationalResponseScore past hPast j : ℝ) =
      FiniteSaddle.ColumnPayoff c.matrix
        (rawHistoryAverage (fun h => (c.rawLawA h).realWeight) past) j := by
  rw [rationalResponseScore, RationalWholeRowLaw.rationalPurePayoff_cast]
  exact c.averageLawA_response_payoff past hPast j

noncomputable def rationalResponseCeiling {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length) : ℚ :=
  finiteRationalMaximum c.actionsB_positive (c.rationalResponseScore past hPast)

theorem rationalResponseCeiling_cast {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length) :
    (c.rationalResponseCeiling past hPast : ℝ) = c.responseCeiling past := by
  apply le_antisymm
  · obtain ⟨j, hj⟩ := finiteRationalMaximum_attained c.actionsB_positive
      (c.rationalResponseScore past hPast)
    change ((finiteRationalMaximum c.actionsB_positive
      (c.rationalResponseScore past hPast) : ℚ) : ℝ) ≤ _
    rw [hj, rationalResponseScore_cast]
    exact FiniteSaddle.column_le_maximizingColumn _ _ _ j
  · let j := FiniteSaddle.maximizingColumn c.actionsB_positive c.matrix
      (rawHistoryAverage (fun h => (c.rawLawA h).realWeight) past)
    have h := le_finiteRationalMaximum c.actionsB_positive
      (c.rationalResponseScore past hPast) j
    have hReal : (c.rationalResponseScore past hPast j : ℝ) ≤
        (c.rationalResponseCeiling past hPast : ℝ) := by exact_mod_cast h
    rw [rationalResponseScore_cast] at hReal
    exact hReal

end ProductSecurityTrainer

namespace FareyUnitSourceInputs
open FareySourceTraining ProductSecurityTrainer

noncomputable def temporalRationalGate {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (richPast poorPast : List (RawObservation (n + 1)))
    (hRich : 0 < richPast.length) (hPoor : 0 < poorPast.length) (tolerance : ℚ) : Bool :=
  decide ((trainer ratio hr values true epsilon he).rationalResponseCeiling richPast hRich +
    (trainer ratio hr values false epsilon he).rationalResponseCeiling poorPast hPoor ≤ 1 + tolerance)

theorem temporalRationalGate_true_iff {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (richPast poorPast : List (RawObservation (n + 1)))
    (hRich : 0 < richPast.length) (hPoor : 0 < poorPast.length) (tolerance : ℚ) :
    temporalRationalGate ratio hr values epsilon he richPast poorPast hRich hPoor tolerance = true ↔
      let richLaw := ((trainer ratio hr values true epsilon he).averageLawA richPast hRich).law
      let poorLaw := ((trainer ratio hr values false epsilon he).averageLawA poorPast hPoor).law
      regret values.values 1 richLaw poorLaw +
        regret values.values (ratio : ℝ) poorLaw richLaw ≤ (tolerance : ℝ) := by
  dsimp only
  have hPair := temporal_pair_gate_iff ratio hr values epsilon he richPast poorPast
    hRich hPoor (tolerance : ℝ)
  dsimp only at hPair
  rw [← hPair]
  unfold temporalRationalGate
  rw [decide_eq_true_eq]
  constructor
  · intro h
    have hReal : ((trainer ratio hr values true epsilon he).rationalResponseCeiling richPast hRich : ℝ) +
        ((trainer ratio hr values false epsilon he).rationalResponseCeiling poorPast hPoor : ℝ) ≤
          1 + (tolerance : ℝ) := by exact_mod_cast h
    simpa only [rationalResponseCeiling_cast] using hReal
  · intro h
    rw [← rationalResponseCeiling_cast _ richPast hRich,
      ← rationalResponseCeiling_cast _ poorPast hPoor] at h
    exact_mod_cast h

theorem temporalRationalGate_sound {n : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1))
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (richPast poorPast : List (RawObservation (n + 1)))
    (hRich : 0 < richPast.length) (hPoor : 0 < poorPast.length) (tolerance : ℚ)
    (hGate : temporalRationalGate ratio hr values epsilon he richPast poorPast hRich hPoor tolerance = true) :
    let richLaw := ((trainer ratio hr values true epsilon he).averageLawA richPast hRich).law
    let poorLaw := ((trainer ratio hr values false epsilon he).averageLawA poorPast hPoor).law
    regret values.values 1 richLaw poorLaw ≤ (tolerance : ℝ) ∧
      regret values.values (ratio : ℝ) poorLaw richLaw ≤ (tolerance : ℝ) := by
  dsimp only
  have hSum := (temporalRationalGate_true_iff ratio hr values epsilon he
    richPast poorPast hRich hPoor tolerance).1 hGate
  dsimp only at hSum
  let richLaw := ((trainer ratio hr values true epsilon he).averageLawA richPast hRich).law
  let poorLaw := ((trainer ratio hr values false epsilon he).averageLawA poorPast hPoor).law
  have hRichNonnegative := regret_nonneg values.values richLaw poorLaw
    (rich_temporal_supported ratio hr values epsilon he richPast hRich)
  have hPoorNonnegative := regret_nonneg values.values poorLaw richLaw
    (poor_temporal_supported ratio hr values epsilon he poorPast hPoor)
  constructor <;> linarith

end FareyUnitSourceInputs
end Blotto
