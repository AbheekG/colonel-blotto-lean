import Blotto.FareyContinuousResponse
import Blotto.FareySourceTraining

/-! Both normalized unit-scale source orientations are constructed from the
positive rational budget ratio. Their finite response domain has a derived
continuous-response envelope; the actual finite payoff bound remains input. -/

namespace Blotto.FareyUnitSourceInputs

open Farey FareySourceTraining
open scoped BigOperators

/-- Candidate-rich means budgets (1,r); candidate-poor means (r,1).
Both actual source inputs use q=r.den and unit field scales. -/
def normalizedInput {m : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector m) (candidateRich : Bool) : Input m where
  q := ratio.den
  q_positive := ratio.den_pos
  scaleA := fun _ => 1
  scaleB := fun _ => 1
  scaleA_nonnegative := by intro _; norm_num
  scaleB_nonnegative := by intro _; norm_num
  budgetA := if candidateRich then 1 else ratio
  budgetB := if candidateRich then ratio else 1
  budgetA_positive := by cases candidateRich <;> simp [hr.1]
  budgetB_positive := by cases candidateRich <;> simp [hr.1]
  values := values

def richCandidateInput {m : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector m) : Input m := normalizedInput ratio hr values true

def poorCandidateInput {m : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector m) : Input m := normalizedInput ratio hr values false

theorem rich_budgets {m : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector m) :
    (richCandidateInput ratio hr values).budgetA = 1 ∧
      (richCandidateInput ratio hr values).budgetB = ratio := by constructor <;> rfl

theorem poor_budgets {m : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector m) :
    (poorCandidateInput ratio hr values).budgetA = ratio ∧
      (poorCandidateInput ratio hr values).budgetB = 1 := by constructor <;> rfl

theorem normalized_q {m : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector m) (candidateRich : Bool) :
    (normalizedInput ratio hr values candidateRich).q = ratio.den := rfl

theorem normalized_scales {m : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector m) (candidateRich : Bool) :
    (∀ j, (normalizedInput ratio hr values candidateRich).scaleA j = 1) ∧
      (∀ j, (normalizedInput ratio hr values candidateRich).scaleB j = 1) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem normalized_q_positive {m : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector m) (candidateRich : Bool) :
    0 < (normalizedInput ratio hr values candidateRich).q := ratio.den_pos

theorem normalized_values {m : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector m) (candidateRich : Bool) :
    (normalizedInput ratio hr values candidateRich).values = values := rfl

theorem normalized_budget_units {m : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector m) (candidateRich : Bool) :
    (normalizedInput ratio hr values candidateRich).budgetA ≤ 1 ∧
      (normalizedInput ratio hr values candidateRich).budgetB ≤ 1 := by
  cases candidateRich <;> simpa [normalizedInput] using hr.2

theorem normalized_budget_guards {m : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector m) (candidateRich : Bool) :
    (0 < (normalizedInput ratio hr values candidateRich).budgetA ∧
      (normalizedInput ratio hr values candidateRich).budgetA ≤ 1) ∧
    (0 < (normalizedInput ratio hr values candidateRich).budgetB ∧
      (normalizedInput ratio hr values candidateRich).budgetB ≤ 1) :=
  ⟨⟨(normalizedInput ratio hr values candidateRich).budgetA_positive,
      (normalized_budget_units ratio hr values candidateRich).1⟩,
    ⟨(normalizedInput ratio hr values candidateRich).budgetB_positive,
      (normalized_budget_units ratio hr values candidateRich).2⟩⟩

/-- The response denominator guard is a consequence of either orientation's
constructed budget, not a certificate supplied to the compiler. -/
theorem normalized_response_den_dvd {m : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector m) (candidateRich : Bool) :
    (normalizedInput ratio hr values candidateRich).budgetB.den ∣
      (normalizedInput ratio hr values candidateRich).q := by
  cases candidateRich <;> simp [normalizedInput]

def order (ratio : ℚ) (n : ℕ) (epsilon : ℚ) : ℕ :=
  sourceOrder ratio.den (n + 1) (quantileCount epsilon)

def candidate (ratio : ℚ) (n : ℕ) (epsilon : ℚ) : RankUniverse :=
  sourceCandidateUniverse ratio.den (n + 1) (quantileCount epsilon) ratio.den_pos

def response (ratio : ℚ) (n : ℕ) (epsilon : ℚ) : RankUniverse :=
  sourceResponseUniverse ratio.den (n + 1) (quantileCount epsilon) ratio.den_pos (by omega)

theorem order_positive (ratio : ℚ) (n : ℕ) (epsilon : ℚ) : 0 < order ratio n epsilon :=
  sourceOrder_positive _ _ _ ratio.den_pos

def trainer {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) : ProductSecurityTrainer (n + 1) :=
  (normalizedInput ratio hr values candidateRich).trainer epsilon he

theorem trainer_sizesA {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (j : Fin (n + 1)) :
    (trainer ratio hr values candidateRich epsilon he).sizesA j = rankCap (order ratio n epsilon) + 1 := rfl

theorem trainer_sizesB {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (j : Fin (n + 1)) :
    (trainer ratio hr values candidateRich epsilon he).sizesB j = rankCap (order ratio n epsilon) + 1 := rfl

theorem trainer_bidsA {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (j : Fin (n + 1))
    (code : Fin ((trainer ratio hr values candidateRich epsilon he).sizesA j)) :
    (trainer ratio hr values candidateRich epsilon he).bidsA j code =
      (candidate ratio n epsilon).decode code.val := by
  change 1 * (candidate ratio n epsilon).decode code.val = _
  exact one_mul _

theorem trainer_bidsB {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (j : Fin (n + 1))
    (code : Fin ((trainer ratio hr values candidateRich epsilon he).sizesB j)) :
    (trainer ratio hr values candidateRich epsilon he).bidsB j code =
      (response ratio n epsilon).decode code.val := by
  change 1 * (response ratio n epsilon).decode code.val = _
  exact one_mul _

theorem trainer_budgetA {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) :
    (trainer ratio hr values candidateRich epsilon he).budgetA =
      (normalizedInput ratio hr values candidateRich).budgetA := rfl

theorem trainer_budgetB {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) :
    (trainer ratio hr values candidateRich epsilon he).budgetB =
      (normalizedInput ratio hr values candidateRich).budgetB := rfl

theorem trainer_values {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) :
    (trainer ratio hr values candidateRich epsilon he).values = values := rfl

/-- Convert bounded natural response labels into the actual dependent finite
code domain of the constructed source trainer. -/
def responseCodesOfNat {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (code : Fin (n + 1) → ℕ) (hCode : ∀ j, code j ≤ rankCap (order ratio n epsilon)) :
    SparseMW.ProductCodes (trainer ratio hr values candidateRich epsilon he).sizesB :=
  fun j => ⟨code j, by rw [trainer_sizesB]; exact Nat.lt_succ_of_le (hCode j)⟩

theorem responseCodesOfNat_val {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (code : Fin (n + 1) → ℕ) (hCode : ∀ j, code j ≤ rankCap (order ratio n epsilon)) (j : Fin (n + 1)) :
    (responseCodesOfNat ratio hr values candidateRich epsilon he code hCode j).val = code j := rfl

theorem responseCodesOfNat_bids {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (code : Fin (n + 1) → ℕ) (hCode : ∀ j, code j ≤ rankCap (order ratio n epsilon)) (j : Fin (n + 1)) :
    (trainer ratio hr values candidateRich epsilon he).bidsB j
      (responseCodesOfNat ratio hr values candidateRich epsilon he code hCode j) =
        (response ratio n epsilon).decode (code j) := by
  rw [trainer_bidsB, responseCodesOfNat_val]

/-- An arbitrary real deviation is represented in the actual response
ProductCodes domain, with the trainer's exact rational resource inequality
and canonical expected payoff against a labelled finite candidate law. -/
theorem continuous_response_productCodes {n labels : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (law : RationalWholeRowLaw labels (n + 1))
    (candidateCode : Fin labels → SparseMW.ProductCodes
      (trainer ratio hr values candidateRich epsilon he).sizesA)
    (hRow : ∀ i j, law.row i j =
      (trainer ratio hr values candidateRich epsilon he).bidsA j (candidateCode i j))
    (y : Allocation (n + 1))
    (hy : Feasible ((trainer ratio hr values candidateRich epsilon he).budgetB : ℝ) y) :
    ∃ code : SparseMW.ProductCodes (trainer ratio hr values candidateRich epsilon he).sizesB,
      SparseMW.productResource (trainer ratio hr values candidateRich epsilon he).bidsB code ≤
        (trainer ratio hr values candidateRich epsilon he).budgetB ∧
      Feasible ((trainer ratio hr values candidateRich epsilon he).budgetB : ℝ)
        (fun j => ((trainer ratio hr values candidateRich epsilon he).bidsB j (code j) : ℝ)) ∧
      purePayoff values.values y law.law = purePayoff values.values
        (fun j => ((trainer ratio hr values candidateRich epsilon he).bidsB j (code j) : ℝ)) law.law := by
  let c := trainer ratio hr values candidateRich epsilon he
  have hCandidateRow : ∀ i j, law.row i j =
      (candidateUniverse (order ratio n epsilon) (order_positive ratio n epsilon)).decode (candidateCode i j).val := by
    intro i j
    rw [hRow, trainer_bidsA]
    rfl
  have hRep : ∃ code : Fin (n + 1) → ℕ,
      (∀ j, code j ≤ rankCap (order ratio n epsilon)) ∧
      Feasible (c.budgetB : ℝ) (fun j => ((response ratio n epsilon).decode (code j) : ℝ)) ∧
      purePayoff values.values y law.law = purePayoff values.values
        (fun j => ((response ratio n epsilon).decode (code j) : ℝ)) law.law := by
    exact candidate_law_continuous_response_represented (order ratio n epsilon) (n + 1) labels ratio.den
      (order_positive ratio n epsilon) (by omega) ratio.den_pos c.budgetB
      (normalized_response_den_dvd ratio hr values candidateRich)
      (normalized_budget_units ratio hr values candidateRich).2
      (fun i j => (candidateCode i j).val) law hCandidateRow values.values y hy
  obtain ⟨code, hCode, hBudget, hPayoff⟩ := hRep
  let finite := responseCodesOfNat ratio hr values candidateRich epsilon he code hCode
  have hBid : ∀ j, c.bidsB j (finite j) = (response ratio n epsilon).decode (code j) :=
    responseCodesOfNat_bids ratio hr values candidateRich epsilon he code hCode
  refine ⟨finite, ?_, ?_, ?_⟩
  · change SparseMW.productResource c.bidsB finite ≤ c.budgetB
    unfold SparseMW.productResource
    simp only [hBid]
    have hSum : (∑ j, ((response ratio n epsilon).decode (code j) : ℝ)) ≤ (c.budgetB : ℝ) := hBudget.2
    exact_mod_cast hSum
  · change Feasible (c.budgetB : ℝ) (fun j => (c.bidsB j (finite j) : ℝ))
    simpa only [hBid] using hBudget
  · change purePayoff values.values y law.law =
      purePayoff values.values (fun j => (c.bidsB j (finite j) : ℝ)) law.law
    simpa only [hBid] using hPayoff

/-- A raw upper bound on the actual finite trainer responses controls every
canonical real deviation. The construction derives both domain membership and
response soundness; it does not derive the finite upper bound itself. -/
theorem finite_response_bound_continuous {n labels : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (law : RationalWholeRowLaw labels (n + 1))
    (candidateCode : Fin labels → SparseMW.ProductCodes
      (trainer ratio hr values candidateRich epsilon he).sizesA)
    (hRow : ∀ i j, law.row i j =
      (trainer ratio hr values candidateRich epsilon he).bidsA j (candidateCode i j))
    (bound : ℝ)
    (hFinite : ∀ code : SparseMW.ProductCodes (trainer ratio hr values candidateRich epsilon he).sizesB,
      SparseMW.productResource (trainer ratio hr values candidateRich epsilon he).bidsB code ≤
        (trainer ratio hr values candidateRich epsilon he).budgetB →
      purePayoff values.values
        (fun j => ((trainer ratio hr values candidateRich epsilon he).bidsB j (code j) : ℝ)) law.law ≤ bound) :
    ∀ y : Allocation (n + 1),
      Feasible ((trainer ratio hr values candidateRich epsilon he).budgetB : ℝ) y →
        purePayoff values.values y law.law ≤ bound := by
  intro y hy
  obtain ⟨code, hResource, _hBudget, hPayoff⟩ :=
    continuous_response_productCodes ratio hr values candidateRich epsilon he law candidateCode hRow y hy
  rw [hPayoff]
  exact hFinite code hResource

/-- Rich-candidate orientation: a finite response bound against the candidate
law controls every real deviation with budget r. -/
theorem rich_candidate_bound_continuous {n labels : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (law : RationalWholeRowLaw labels (n + 1))
    (candidateCode : Fin labels → SparseMW.ProductCodes
      ((richCandidateInput ratio hr values).trainer epsilon he).sizesA)
    (hRow : ∀ i j, law.row i j =
      ((richCandidateInput ratio hr values).trainer epsilon he).bidsA j (candidateCode i j))
    (bound : ℝ)
    (hFinite : ∀ code : SparseMW.ProductCodes ((richCandidateInput ratio hr values).trainer epsilon he).sizesB,
      SparseMW.productResource ((richCandidateInput ratio hr values).trainer epsilon he).bidsB code ≤ ratio →
      purePayoff values.values
        (fun j => (((richCandidateInput ratio hr values).trainer epsilon he).bidsB j (code j) : ℝ)) law.law ≤ bound) :
    ∀ y : Allocation (n + 1), Feasible (ratio : ℝ) y → purePayoff values.values y law.law ≤ bound :=
  finite_response_bound_continuous ratio hr values true epsilon he law candidateCode hRow bound hFinite

/-- Poor-candidate orientation: a finite response bound against the candidate
law controls every real deviation with budget one. -/
theorem poor_candidate_bound_continuous {n labels : ℕ}
    (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (law : RationalWholeRowLaw labels (n + 1))
    (candidateCode : Fin labels → SparseMW.ProductCodes
      ((poorCandidateInput ratio hr values).trainer epsilon he).sizesA)
    (hRow : ∀ i j, law.row i j =
      ((poorCandidateInput ratio hr values).trainer epsilon he).bidsA j (candidateCode i j))
    (bound : ℝ)
    (hFinite : ∀ code : SparseMW.ProductCodes ((poorCandidateInput ratio hr values).trainer epsilon he).sizesB,
      SparseMW.productResource ((poorCandidateInput ratio hr values).trainer epsilon he).bidsB code ≤ 1 →
      purePayoff values.values
        (fun j => (((poorCandidateInput ratio hr values).trainer epsilon he).bidsB j (code j) : ℝ)) law.law ≤ bound) :
    ∀ y : Allocation (n + 1), Feasible 1 y → purePayoff values.values y law.law ≤ bound := by
  have h := finite_response_bound_continuous ratio hr values false epsilon he law candidateCode hRow bound hFinite
  change ∀ y : Allocation (n + 1), Feasible ((1 : ℚ) : ℝ) y → purePayoff values.values y law.law ≤ bound at h
  simpa only [Rat.cast_one] using h

end Blotto.FareyUnitSourceInputs
