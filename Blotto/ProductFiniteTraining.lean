import Blotto.ProductSamplerLawContract
import Blotto.RationalFiniteKernel
import Blotto.FiniteAdaptiveExpectation

/-! Finite whole-row training observations use independent player labels and
one value-weighted battlefield label. Their conditional single-field loss mean
is the full payoff against the opposing whole mixed law, with canonical half
ties including zero. Rational arrays and their bounded local samplers are
explicit; compact product implementation and learner convergence are separate. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators Classical

structure RationalWholeRowLaw (labels fields : ℕ) where
  weight : Fin labels → ℚ
  nonnegative : ∀ i, 0 ≤ weight i
  sum_one : ∑ i, weight i = 1
  row : Fin labels → Fin fields → ℚ

namespace RationalWholeRowLaw

noncomputable def realRow {r m : ℕ} (a : RationalWholeRowLaw r m) (i : Fin r) : Allocation m :=
  fun j => (a.row i j : ℝ)

noncomputable def realWeight {r m : ℕ} (a : RationalWholeRowLaw r m) (i : Fin r) : ℝ := a.weight i

theorem realWeight_nonnegative {r m : ℕ} (a : RationalWholeRowLaw r m) (i : Fin r) :
    0 ≤ a.realWeight i := by
  change (0 : ℝ) ≤ (a.weight i : ℝ)
  exact_mod_cast a.nonnegative i

theorem realWeight_sum {r m : ℕ} (a : RationalWholeRowLaw r m) : ∑ i, a.realWeight i = 1 := by
  change (∑ i, (a.weight i : ℝ)) = 1
  exact_mod_cast a.sum_one

noncomputable def law {r m : ℕ} (a : RationalWholeRowLaw r m) : Mixed m :=
  probabilityMixture a.realWeight (fun i => ProductBidTree.allocationPointLaw (a.realRow i))
    a.realWeight_nonnegative a.realWeight_sum

theorem law_event {r m : ℕ} (a : RationalWholeRowLaw r m) (event : Set (Allocation m))
    (hEvent : MeasurableSet event) :
    (a.law : Measure (Allocation m)).real event =
      ∑ i, a.realWeight i * (if a.realRow i ∈ event then 1 else 0) := by
  unfold law
  rw [probabilityMixture_real_apply _ _ _ _ _ hEvent]
  apply Finset.sum_congr rfl
  intro i _
  change a.realWeight i * (Measure.dirac (a.realRow i)).real event = _
  rw [Measure.real, Measure.dirac_apply' _ hEvent]
  by_cases hi : a.realRow i ∈ event <;> simp [hi]

theorem purePayoff_eq_sum {r m : ℕ} (a : RationalWholeRowLaw r m) (values : Values m)
    (candidate : Allocation m) :
    purePayoff values candidate a.law = ∑ i, a.realWeight i * payoff values candidate (a.realRow i) := by
  rw [purePayoff_marginals]
  have hStrict : ∀ j, strictCDF a.law j (candidate j) =
      ∑ i, a.realWeight i * (if (a.realRow i) j < candidate j then 1 else 0) := by
    intro j
    unfold strictCDF marginal
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [map_measureReal_apply (measurable_pi_apply j) measurableSet_Iio]
    exact a.law_event {row | row j < candidate j}
      (measurableSet_lt (measurable_pi_apply j) measurable_const)
  have hClosed : ∀ j, closedCDF a.law j (candidate j) =
      ∑ i, a.realWeight i * (if (a.realRow i) j ≤ candidate j then 1 else 0) := by
    intro j
    unfold closedCDF marginal
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [map_measureReal_apply (measurable_pi_apply j) measurableSet_Iic]
    exact a.law_event {row | row j ≤ candidate j}
      (measurableSet_le (measurable_pi_apply j) measurable_const)
  simp_rw [hStrict, hClosed]
  unfold payoff
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hShare : share (candidate j) ((a.realRow i) j) =
      ((if (a.realRow i) j < candidate j then 1 else 0) +
        (if (a.realRow i) j ≤ candidate j then 1 else 0)) / 2 := by
    rw [share_indicator]
    simp only [Set.indicator_apply, mem_Iio, mem_Iic]
    ring
  rw [hShare]
  ring

theorem law_supported {r m : ℕ} (a : RationalWholeRowLaw r m) (budget : ℝ)
    (h : ∀ i, Feasible budget (a.realRow i)) : Supported budget a.law := by
  apply probabilityMixture_supported
  intro i
  change ∀ᵐ row ∂Measure.dirac (a.realRow i), Feasible budget row
  rw [ae_dirac_eq]
  exact h i

def labelAttempt {r m : ℕ} (a : RationalWholeRowLaw r m) (fallback : Fin r) : RationalFiniteAttempt r r where
  weight := a.weight
  nonnegative := a.nonnegative
  sum_one := a.sum_one
  decode := some
  fallbackLabel := fallback

end RationalWholeRowLaw

structure RationalFieldSelector (fields : ℕ) where
  weight : Fin fields → ℚ
  positive : ∀ j, 0 < weight j
  sum_one : ∑ j, weight j = 1

namespace RationalFieldSelector

noncomputable def values {m : ℕ} (v : RationalFieldSelector m) : Values m where
  weight := fun j => (v.weight j : ℝ)
  positive := by intro j; exact_mod_cast v.positive j
  normalized := by exact_mod_cast v.sum_one

theorem fields_positive {m : ℕ} (v : RationalFieldSelector m) : 0 < m := by
  by_contra hn
  have hz : m = 0 := by omega
  subst m
  have hs := v.sum_one
  simp at hs

def attempt {m : ℕ} (v : RationalFieldSelector m) : RationalFiniteAttempt m m where
  weight := v.weight
  nonnegative := fun j => (v.positive j).le
  sum_one := v.sum_one
  decode := some
  fallbackLabel := ⟨0, v.fields_positive⟩

theorem attempt_idealMean {m : ℕ} (v : RationalFieldSelector m) (f : Option (Fin m) → ℝ) :
    v.attempt.idealMean f = ∑ j, (v.weight j : ℝ) * f (some j) := rfl

end RationalFieldSelector

namespace ProductFiniteTraining

abbrev Observation (r s m : ℕ) := Fin r × Fin s × Fin m

def probability {r s m : ℕ} (a : RationalWholeRowLaw r m) (b : RationalWholeRowLaw s m)
    (v : RationalFieldSelector m) (observed : Observation r s m) : ℚ :=
  a.weight observed.1 * b.weight observed.2.1 * v.weight observed.2.2

theorem probability_nonnegative {r s m : ℕ} (a : RationalWholeRowLaw r m) (b : RationalWholeRowLaw s m)
    (v : RationalFieldSelector m) (observed : Observation r s m) : 0 ≤ probability a b v observed :=
  mul_nonneg (mul_nonneg (a.nonnegative _) (b.nonnegative _)) (v.positive _).le

theorem probability_sum {r s m : ℕ} (a : RationalWholeRowLaw r m) (b : RationalWholeRowLaw s m)
    (v : RationalFieldSelector m) : ∑ observed, probability a b v observed = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [probability, Fintype.sum_prod_type]
  have hField : ∀ i j, (∑ field, a.weight i * b.weight j * v.weight field) = a.weight i * b.weight j := by
    intro i j
    rw [← Finset.mul_sum, v.sum_one, mul_one]
  simp_rw [hField]
  have hOpponent : ∀ i, (∑ j, a.weight i * b.weight j) = a.weight i := by
    intro i
    rw [← Finset.mul_sum, b.sum_one, mul_one]
  simp_rw [hOpponent]
  exact a.sum_one

def observationEquiv (r s m : ℕ) : Observation r s m ≃ Fin (r * (s * m)) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv

def indexedProbability {r s m : ℕ} (a : RationalWholeRowLaw r m) (b : RationalWholeRowLaw s m)
    (v : RationalFieldSelector m) (observed : Fin (r * (s * m))) : ℚ :=
  probability a b v ((observationEquiv r s m).symm observed)

theorem indexedProbability_nonnegative {r s m : ℕ} (a : RationalWholeRowLaw r m) (b : RationalWholeRowLaw s m)
    (v : RationalFieldSelector m) (observed : Fin (r * (s * m))) : 0 ≤ indexedProbability a b v observed :=
  probability_nonnegative a b v _

theorem indexedProbability_sum {r s m : ℕ} (a : RationalWholeRowLaw r m) (b : RationalWholeRowLaw s m)
    (v : RationalFieldSelector m) : ∑ observed, indexedProbability a b v observed = 1 := by
  rw [← Equiv.sum_comp (observationEquiv r s m)]
  simp only [indexedProbability, Equiv.symm_apply_apply]
  exact probability_sum a b v

noncomputable def empiricalLossA {r s m : ℕ} (b : RationalWholeRowLaw s m)
    (candidate : Allocation m) (observed : Observation r s m) : ℝ :=
  share (candidate observed.2.2) (b.realRow observed.2.1 observed.2.2)

noncomputable def empiricalLossB {r s m : ℕ} (a : RationalWholeRowLaw r m)
    (candidate : Allocation m) (observed : Observation r s m) : ℝ :=
  share (candidate observed.2.2) (a.realRow observed.1 observed.2.2)

theorem empiricalLossA_unit {r s m : ℕ} (b : RationalWholeRowLaw s m)
    (candidate : Allocation m) (observed : Observation r s m) :
    0 ≤ empiricalLossA b candidate observed ∧ empiricalLossA b candidate observed ≤ 1 :=
  ⟨share_nonneg _ _, share_le_one _ _⟩

theorem empiricalLossB_unit {r s m : ℕ} (a : RationalWholeRowLaw r m)
    (candidate : Allocation m) (observed : Observation r s m) :
    0 ≤ empiricalLossB a candidate observed ∧ empiricalLossB a candidate observed ≤ 1 :=
  ⟨share_nonneg _ _, share_le_one _ _⟩

-- Security learning minimizes the response's payoff against a candidate.
-- These reversed-share losses make that orientation explicit.
noncomputable def opposingLossA {r s m : ℕ} (b : RationalWholeRowLaw s m)
    (candidate : Allocation m) (observed : Observation r s m) : ℝ :=
  share (b.realRow observed.2.1 observed.2.2) (candidate observed.2.2)

noncomputable def opposingLossB {r s m : ℕ} (a : RationalWholeRowLaw r m)
    (candidate : Allocation m) (observed : Observation r s m) : ℝ :=
  share (a.realRow observed.1 observed.2.2) (candidate observed.2.2)

theorem opposingLossA_unit {r s m : ℕ} (b : RationalWholeRowLaw s m)
    (candidate : Allocation m) (observed : Observation r s m) :
    0 ≤ opposingLossA b candidate observed ∧ opposingLossA b candidate observed ≤ 1 :=
  ⟨share_nonneg _ _, share_le_one _ _⟩

theorem opposingLossB_unit {r s m : ℕ} (a : RationalWholeRowLaw r m)
    (candidate : Allocation m) (observed : Observation r s m) :
    0 ≤ opposingLossB a candidate observed ∧ opposingLossB a candidate observed ≤ 1 :=
  ⟨share_nonneg _ _, share_le_one _ _⟩

theorem opposingLossA_complement {r s m : ℕ} (b : RationalWholeRowLaw s m)
    (candidate : Allocation m) (observed : Observation r s m) :
    opposingLossA b candidate observed = 1 - empiricalLossA b candidate observed := by
  have h := share_constant_sum (candidate observed.2.2) (b.realRow observed.2.1 observed.2.2)
  unfold opposingLossA empiricalLossA
  linarith

theorem conditionalLossA {r s m : ℕ} (a : RationalWholeRowLaw r m) (b : RationalWholeRowLaw s m)
    (v : RationalFieldSelector m) (candidate : Allocation m) :
    (∑ observed, (probability a b v observed : ℝ) * empiricalLossA b candidate observed) =
      purePayoff v.values candidate b.law := by
  rw [b.purePayoff_eq_sum]
  rw [Fintype.sum_prod_type]
  simp only [probability, empiricalLossA, Rat.cast_mul]
  simp_rw [Fintype.sum_prod_type]
  have hFactor : ∀ i, (∑ j, ∑ field,
      (a.weight i : ℝ) * (b.weight j : ℝ) * (v.weight field : ℝ) * share (candidate field) (b.realRow j field)) =
      (a.weight i : ℝ) * (∑ j, (b.weight j : ℝ) * payoff v.values candidate (b.realRow j)) := by
    intro i
    simp only [payoff, RationalFieldSelector.values]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro field _
    ring
  simp_rw [hFactor]
  rw [← Finset.sum_mul]
  have ha : (∑ i, (a.weight i : ℝ)) = 1 := by exact_mod_cast a.sum_one
  rw [ha, one_mul]
  rfl

theorem conditionalLossB {r s m : ℕ} (a : RationalWholeRowLaw r m) (b : RationalWholeRowLaw s m)
    (v : RationalFieldSelector m) (candidate : Allocation m) :
    (∑ observed, (probability a b v observed : ℝ) * empiricalLossB a candidate observed) =
      purePayoff v.values candidate a.law := by
  rw [a.purePayoff_eq_sum]
  rw [Fintype.sum_prod_type]
  simp only [probability, empiricalLossB, Rat.cast_mul]
  simp_rw [Fintype.sum_prod_type]
  have hFactor : ∀ i, (∑ j, ∑ field,
      (a.weight i : ℝ) * (b.weight j : ℝ) * (v.weight field : ℝ) * share (candidate field) (a.realRow i field)) =
      (a.weight i : ℝ) * payoff v.values candidate (a.realRow i) := by
    intro i
    rw [Finset.sum_comm]
    have hb : (∑ j, (b.weight j : ℝ)) = 1 := by exact_mod_cast b.sum_one
    simp only [payoff, RationalFieldSelector.values]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro field _
    have he : (∑ j, (a.weight i : ℝ) * (b.weight j : ℝ) * (v.weight field : ℝ) *
        share (candidate field) (a.realRow i field)) =
        (a.weight i : ℝ) * ((v.weight field : ℝ) * share (candidate field) (a.realRow i field)) := by
      calc
        _ = ((a.weight i : ℝ) * ((v.weight field : ℝ) * share (candidate field) (a.realRow i field))) *
            ∑ j, (b.weight j : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [hb, mul_one]
    exact he
  simp_rw [hFactor]
  rfl

theorem conditionalLossA_bias {r s m : ℕ} (a : RationalWholeRowLaw r m) (b : RationalWholeRowLaw s m)
    (v : RationalFieldSelector m) (candidate : Allocation m) (target : Mixed m) (delta : ℝ)
    (h : CDFClose b.law target delta) :
    |(∑ observed, (probability a b v observed : ℝ) * empiricalLossA b candidate observed) -
      purePayoff v.values candidate target| ≤ delta := by
  rw [conditionalLossA]
  exact purePayoff_close v.values h candidate

theorem conditionalOpposingLossA {r s m : ℕ} (a : RationalWholeRowLaw r m) (b : RationalWholeRowLaw s m)
    (v : RationalFieldSelector m) (candidate : Allocation m) :
    (∑ observed, (probability a b v observed : ℝ) * opposingLossA b candidate observed) =
      1 - purePayoff v.values candidate b.law := by
  simp_rw [opposingLossA_complement, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, conditionalLossA]
  have hp : (∑ observed, (probability a b v observed : ℝ)) = 1 := by
    exact_mod_cast probability_sum a b v
  rw [hp]

theorem conditionalOpposingLossA_bias {r s m : ℕ} (a : RationalWholeRowLaw r m) (b : RationalWholeRowLaw s m)
    (v : RationalFieldSelector m) (candidate : Allocation m) (target : Mixed m) (delta : ℝ)
    (h : CDFClose b.law target delta) :
    |(∑ observed, (probability a b v observed : ℝ) * opposingLossA b candidate observed) -
      (1 - purePayoff v.values candidate target)| ≤ delta := by
  rw [conditionalOpposingLossA]
  have he : (1 - purePayoff v.values candidate b.law) - (1 - purePayoff v.values candidate target) =
      -(purePayoff v.values candidate b.law - purePayoff v.values candidate target) := by ring
  rw [he, abs_neg]
  exact purePayoff_close v.values h candidate

theorem indexed_conditionalOpposingLossA {r s m : ℕ} (a : RationalWholeRowLaw r m) (b : RationalWholeRowLaw s m)
    (v : RationalFieldSelector m) (candidate : Allocation m) :
    (∑ observed, (indexedProbability a b v observed : ℝ) *
      opposingLossA b candidate ((observationEquiv r s m).symm observed)) =
        1 - purePayoff v.values candidate b.law := by
  rw [← Equiv.sum_comp (observationEquiv r s m)]
  simp only [indexedProbability, Equiv.symm_apply_apply]
  exact conditionalOpposingLossA a b v candidate

theorem indexed_conditionalLossA {r s m : ℕ} (a : RationalWholeRowLaw r m) (b : RationalWholeRowLaw s m)
    (v : RationalFieldSelector m) (candidate : Allocation m) :
    (∑ observed, (indexedProbability a b v observed : ℝ) *
      empiricalLossA b candidate ((observationEquiv r s m).symm observed)) = purePayoff v.values candidate b.law := by
  rw [← Equiv.sum_comp (observationEquiv r s m)]
  simp only [indexedProbability, Equiv.symm_apply_apply]
  exact conditionalLossA a b v candidate

end ProductFiniteTraining
end Blotto
