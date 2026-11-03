import Blotto.DeterministicQuantileRounding
import Blotto.ContinuousSecurityValues
import Blotto.BudgetScaling

/-! Finite downward quantile rounding of an arbitrary feasible whole law.
Every coordinate map acts on the SAME original allocation. The actual joint
pushforward remains hard-budget feasible, uses at most K^n labelled rows,
and changes either canonical marginal CDF by at most 1/K. Zero and positive
atoms, repeated anchors, singular laws and partial spending are included.
No uniform marginal label weights, marginal-to-coupling oracle, rational
order-cell witness, minimax equality or efficient output access is asserted. -/

namespace Blotto.WholeQuantileRounding
open MeasureTheory Set QuantileCDFWitness
open scoped BigOperators Classical

theorem marginal_unitSupported {n : ℕ} (law : Mixed n) (budget : ℝ)
    (hBudget : budget ≤ 1) (hLaw : Supported budget law) (j : Fin n) :
    UnitSupported (marginal law j) := by
  change ∀ᵐ x ∂Measure.map (fun row : Allocation n => row j) (law : Measure (Allocation n)),
    x ∈ Icc (0 : ℝ) 1
  apply (ae_map_iff (measurable_pi_apply j).aemeasurable measurableSet_Icc).mpr
  exact hLaw.mono fun row hRow =>
    ⟨hRow.1 j, (PureBoundaryEquilibria.feasible_coordinate_le hRow j).trans hBudget⟩

noncomputable def roundRow {n : ℕ} (law : Mixed n) (K : ℕ) (hK : 0 < K)
    (row : Allocation n) : Allocation n :=
  fun j => DeterministicQuantileRounding.round (marginal law j) K hK (row j)

theorem roundRow_measurable {n : ℕ} (law : Mixed n) (budget : ℝ)
    (hBudget : budget ≤ 1) (hLaw : Supported budget law) (K : ℕ) (hK : 0 < K) :
    Measurable (roundRow law K hK) := by
  apply Measurable.of_eval
  intro j
  exact (DeterministicQuantileRounding.round_measurable (marginal law j)
    (marginal_unitSupported law budget hBudget hLaw j) K hK).comp (measurable_pi_apply j)

theorem roundRow_downward {n : ℕ} (law : Mixed n) (K : ℕ) (hK : 0 < K)
    (row : Allocation n) (hRow : ∀ j, 0 ≤ row j) :
    ∀ j, roundRow law K hK row j ≤ row j :=
  fun j => DeterministicQuantileRounding.round_le _ _ _ _ (hRow j)

theorem roundRow_feasible {n : ℕ} (law : Mixed n) (K : ℕ) (hK : 0 < K)
    (budget : ℝ) (row : Allocation n) (hRow : Feasible budget row) :
    Feasible budget (roundRow law K hK row) := by
  refine ⟨fun j => DeterministicQuantileRounding.round_nonnegative _ _ _ _, ?_⟩
  exact (Finset.sum_le_sum fun j _ => roundRow_downward law K hK row hRow.1 j).trans hRow.2

noncomputable def roundedLaw {n : ℕ} (law : Mixed n) (K : ℕ) (hK : 0 < K) : Mixed n :=
  law.map (roundRow law K hK)

theorem roundedLaw_supported {n : ℕ} (law : Mixed n) (budget : ℝ)
    (hBudget : budget ≤ 1) (hLaw : Supported budget law) (K : ℕ) (hK : 0 < K) :
    Supported budget (roundedLaw law K hK) := by
  change ∀ᵐ row ∂Measure.map (roundRow law K hK) (law : Measure (Allocation n)), Feasible budget row
  rw [ae_map_iff (roundRow_measurable law budget hBudget hLaw K hK).aemeasurable (measurable_feasible budget)]
  exact hLaw.mono fun row hRow => roundRow_feasible law K hK budget row hRow

theorem roundedLaw_marginal {n : ℕ} (law : Mixed n) (budget : ℝ)
    (hBudget : budget ≤ 1) (hLaw : Supported budget law) (K : ℕ) (hK : 0 < K) (j : Fin n) :
    marginal (roundedLaw law K hK) j =
      DeterministicQuantileRounding.roundedLaw (marginal law j) K hK := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun row : Allocation n => row j)
      (Measure.map (roundRow law K hK) (law : Measure (Allocation n))) =
    Measure.map (DeterministicQuantileRounding.round (marginal law j) K hK)
      (Measure.map (fun row : Allocation n => row j) (law : Measure (Allocation n)))
  rw [Measure.map_map (measurable_pi_apply j) (roundRow_measurable law budget hBudget hLaw K hK),
    Measure.map_map (DeterministicQuantileRounding.round_measurable (marginal law j)
      (marginal_unitSupported law budget hBudget hLaw j) K hK) (measurable_pi_apply j)]
  rfl

theorem roundedLaw_CDFClose {n : ℕ} (law : Mixed n) (budget : ℝ)
    (hBudget : budget ≤ 1) (hLaw : Supported budget law) (K : ℕ) (hK : 0 < K) :
    CDFClose law (roundedLaw law K hK) (1 / K) := by
  intro j t
  unfold closedCDF
  rw [roundedLaw_marginal law budget hBudget hLaw K hK j]
  exact DeterministicQuantileRounding.closed_cdf_error _
    (marginal_unitSupported law budget hBudget hLaw j) K hK t

theorem roundedLaw_both_cdf_increases {n : ℕ} (law : Mixed n) (budget : ℝ)
    (hBudget : budget ≤ 1) (hLaw : Supported budget law) (K : ℕ) (hK : 0 < K)
    (j : Fin n) (t : ℝ) :
    0 ≤ closedCDF (roundedLaw law K hK) j t - closedCDF law j t ∧
      closedCDF (roundedLaw law K hK) j t - closedCDF law j t ≤ 1 / K ∧
    0 ≤ strictCDF (roundedLaw law K hK) j t - strictCDF law j t ∧
      strictCDF (roundedLaw law K hK) j t - strictCDF law j t ≤ 1 / K := by
  unfold closedCDF strictCDF
  rw [roundedLaw_marginal law budget hBudget hLaw K hK j]
  exact DeterministicQuantileRounding.both_cdf_increases _
    (marginal_unitSupported law budget hBudget hLaw j) K hK t

noncomputable def labelledRow {n : ℕ} (law : Mixed n) (K : ℕ)
    (labels : Fin n → Fin K) : Allocation n :=
  fun j => DeterministicQuantileRounding.anchor (marginal law j) K (labels j)

noncomputable def finiteRows {n : ℕ} (law : Mixed n) (K : ℕ) : Finset (Allocation n) :=
  Finset.univ.image (labelledRow law K)

theorem finiteRows_card {n : ℕ} (law : Mixed n) (K : ℕ) :
    (finiteRows law K).card ≤ K ^ n := by
  have h := Finset.card_image_le (f := labelledRow law K) (s := Finset.univ)
  simpa only [finiteRows, Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using h

theorem roundRow_mem_finiteRows {n : ℕ} (law : Mixed n) (K : ℕ) (hK : 0 < K)
    (row : Allocation n) : roundRow law K hK row ∈ finiteRows law K := by
  have hLabels : ∀ j : Fin n, ∃ label : Fin K,
      roundRow law K hK row j = DeterministicQuantileRounding.anchor (marginal law j) K label :=
    fun j => DeterministicQuantileRounding.round_mem_anchors _ K hK (row j)
  choose labels hLabels using hLabels
  refine Finset.mem_image.mpr ⟨labels, Finset.mem_univ _, ?_⟩
  exact (funext hLabels).symm

theorem roundedLaw_finite_supported {n : ℕ} (law : Mixed n) (budget : ℝ)
    (hBudget : budget ≤ 1) (hLaw : Supported budget law) (K : ℕ) (hK : 0 < K) :
    ∀ᵐ row ∂(roundedLaw law K hK : Measure (Allocation n)),
      row ∈ (finiteRows law K : Set (Allocation n)) ∧ Feasible budget row := by
  change ∀ᵐ row ∂Measure.map (roundRow law K hK) (law : Measure (Allocation n)), _
  apply (ae_map_iff (roundRow_measurable law budget hBudget hLaw K hK).aemeasurable
    (((finiteRows law K).finite_toSet.measurableSet).inter (measurable_feasible budget))).mpr
  exact hLaw.mono fun row hRow =>
    ⟨roundRow_mem_finiteRows law K hK row, roundRow_feasible law K hK budget row hRow⟩

theorem roundedLaw_response_bound {n : ℕ} (values : Values n) (law : Mixed n) (budget : ℝ)
    (hBudget : budget ≤ 1) (hLaw : Supported budget law) (K : ℕ) (hK : 0 < K)
    (deviation : Allocation n) :
    purePayoff values deviation (roundedLaw law K hK) ≤ purePayoff values deviation law + 1 / K := by
  have h := abs_le.mp (purePayoff_close values (roundedLaw_CDFClose law budget hBudget hLaw K hK) deviation)
  linarith

theorem roundedLaw_security_bound {n : ℕ} (values : Values n) (law : Mixed n) (budget : ℝ)
    (hBudget : budget ≤ 1) (hLaw : Supported budget law) (K : ℕ) (hK : 0 < K)
    (opposingBudget : ℝ) (hOpposing : 0 ≤ opposingBudget) :
    security values opposingBudget (roundedLaw law K hK) ≤ security values opposingBudget law + 1 / K := by
  have h := abs_le.mp (security_close values hOpposing (roundedLaw_CDFClose law budget hBudget hLaw K hK))
  linarith

/-- The unknown near-optimal comparator is rounded while keeping its original
whole-allocation coupling. Rationalizing these finitely many anchors remains
the next R42 obligation; no Farey-domain comparator is supplied by this lemma. -/
theorem exists_finite_near_optimal {n : ℕ} (values : Values n) (budget opposingBudget : ℝ)
    (hBudget : 0 ≤ budget ∧ budget ≤ 1) (hOpposing : 0 ≤ opposingBudget)
    (error : ℝ) (hError : 0 < error) (K : ℕ) (hK : 0 < K) :
    ∃ law : Mixed n, Supported budget law ∧
      (∃ rows : Finset (Allocation n), rows.card ≤ K ^ n ∧
        ∀ᵐ row ∂(law : Measure (Allocation n)), row ∈ (rows : Set (Allocation n))) ∧
      security values opposingBudget law <
        ContinuousSecurityValues.lossInfimum values budget opposingBudget + error + 1 / K := by
  obtain ⟨original, hOriginal, hNear⟩ :=
    ContinuousSecurityValues.exists_near_optimal values budget opposingBudget hBudget.1 hOpposing error hError
  refine ⟨roundedLaw original K hK, roundedLaw_supported original budget hBudget.2 hOriginal K hK,
    ⟨finiteRows original K, finiteRows_card original K, ?_⟩, ?_⟩
  · exact (roundedLaw_finite_supported original budget hBudget.2 hOriginal K hK).mono fun _ h => h.1
  · exact (roundedLaw_security_bound values original budget hBudget.2 hOriginal K hK opposingBudget hOpposing).trans_lt
      (by linarith)

end Blotto.WholeQuantileRounding
