import Blotto.WholeQuantileRationalSecurity
import Blotto.FareyUnitSourceInputs
import Blotto.ProductSecurityComparator

/-! Actual R42 comparator membership in BOTH normalized Farey source
trainers. The same original draw yields a feasible rational catalogue law
using the retained D=q(m+2)^[m(K-1)+1]. Every reached row has an actual
closed source code. Its real probabilities are retained, and the source's
finite response floor is bounded by continuous security plus 1/K.
No minimax equality, accepted trial, enumeration price or sampler is supplied. -/

namespace Blotto.WholeQuantileFareyComparator
open MeasureTheory Set Farey FareySourceTraining FareyUnitSourceInputs
open RationalOrderCell WholeQuantileOrderCell WholeQuantileRationalTransport WholeQuantileRationalSecurity
open scoped BigOperators Classical

theorem quantileCount_positive (epsilon : ℚ) (he : 0 < epsilon) : 0 < quantileCount epsilon := by
  by_contra hn
  have hz : quantileCount epsilon = 0 := by omega
  have h := quantileCount_guard epsilon he
  rw [hz] at h
  norm_num at h

theorem quantile_error_le (epsilon : ℚ) (he : 0 < epsilon) :
    1 / (quantileCount epsilon : ℝ) ≤ (epsilon : ℝ) / 64 := by
  have hk : (0 : ℝ) < quantileCount epsilon := by exact_mod_cast quantileCount_positive epsilon he
  have hg : (64 : ℝ) ≤ (quantileCount epsilon : ℝ) * (epsilon : ℝ) := by
    exact_mod_cast quantileCount_guard epsilon he
  apply (div_le_iff₀ hk).mpr
  nlinarith

def budgetPair {m : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector m) (candidateRich : Bool) : Fin 2 → ℚ :=
  ![(normalizedInput ratio hr values candidateRich).budgetA,
    (normalizedInput ratio hr values candidateRich).budgetB]

theorem budgetPair_denominator {m : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector m) (candidateRich : Bool) :
    commonDenominator (budgetPair ratio hr values candidateRich) = ratio.den := by
  cases candidateRich <;> simp [commonDenominator,budgetPair,normalizedInput]

/-- The concrete source code for a rational bid is its distinguished closed
Farey code, not an abstract membership label. -/
def candidateCodesOfRat {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (row : Fin (n + 1) → ℚ)
    (hUnit : ∀ field, 0 ≤ row field ∧ row field ≤ 1) :
    SparseMW.ProductCodes (trainer ratio hr values candidateRich epsilon he).sizesA :=
  fun field => ⟨closedCode (order ratio n epsilon) (fractionOfRat (row field)),by
    rw [trainer_sizesA]
    apply Nat.lt_succ_of_le
    apply closedCode_le_rankCap _ (order_positive ratio n epsilon)
    rw [fractionOfRat_value _ (hUnit field).1]
    exact (hUnit field).2⟩

theorem candidateCodesOfRat_bids {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (row : Fin (n + 1) → ℚ)
    (hUnit : ∀ field, 0 ≤ row field ∧ row field ≤ 1)
    (hDen : ∀ field, (row field).den ≤ order ratio n epsilon) (field : Fin (n + 1)) :
    (trainer ratio hr values candidateRich epsilon he).bidsA field
      (candidateCodesOfRat ratio hr values candidateRich epsilon he row hUnit field) = row field := by
  rw [trainer_bidsA]
  exact (decode_closed_bid (candidate ratio n epsilon) (fractionOfRat (row field))
    (hDen field) (by rw [fractionOfRat_value _ (hUnit field).1]; exact (hUnit field).2)).trans
      (fractionOfRat_value _ (hUnit field).1)

/-- Every supported law has a concrete comparator in the actual normalized
source candidate domain. No rational-weight or uniform-label conversion is
needed for the resulting semantic finite-floor bound. -/
theorem exists_source_comparator {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (law : Mixed (n + 1))
    (hLaw : Supported ((normalizedInput ratio hr values candidateRich).budgetA : ℝ) law) :
    let c := trainer ratio hr values candidateRich epsilon he
    ∃ comparator : Mixed (n + 1), Supported (c.budgetA : ℝ) comparator ∧
      (∀ᵐ row ∂(comparator : Measure (Allocation (n + 1))),
        ∃ code : SparseMW.ProductCodes c.sizesA,
          SparseMW.productResource c.bidsA code ≤ c.budgetA ∧
          row = fun field => (c.bidsA field (code field) : ℝ)) ∧
      security values.values (c.budgetB : ℝ) comparator ≤
        security values.values (c.budgetB : ℝ) law + 1 / quantileCount epsilon := by
  let K := quantileCount epsilon
  have hK : 0 < K := quantileCount_positive epsilon he.1
  let budgets := budgetPair ratio hr values candidateRich
  have hOwn : (budgets 0 : ℝ) ≤ 1 := by
    exact_mod_cast (normalized_budget_units ratio hr values candidateRich).1
  have hOriginal : Supported (budgets 0 : ℝ) law := hLaw
  obtain ⟨coordinates,hCell,hMargin,denominator,hPositive,hBound,hDivides,_⟩ :=
    exists_rational_catalogue law (budgets 0 : ℝ) hOwn hOriginal K hK budgets
  let result := transportedLaw law hK coordinates
  have hSupported : Supported (budgets 0 : ℝ) result :=
    transportedLaw_supported law hK budgets coordinates hCell hMargin 0 hOwn hOriginal
  have hFinite := transportedLaw_finite_supported law hK budgets coordinates hCell hMargin _ hOwn hOriginal
  have hDenBound : denominator ≤ order ratio n epsilon := by
    rw [budgetPair_denominator] at hBound
    exact hBound
  let c := trainer ratio hr values candidateRich epsilon he
  refine ⟨result,hSupported,?_,?_⟩
  · exact (hFinite.and hSupported).mono fun row hrowFacts => by
      obtain ⟨labels,_,hRow⟩ := Finset.mem_image.mp hrowFacts.1
      let rational := rationalRow coordinates labels
      have hUnit : ∀ field, 0 ≤ rational field ∧ rational field ≤ 1 := by
        intro field
        have h := rationalRef_unit _ (fun v => feasible_unit budgets (original law K) _ hCell (some v))
          (tupleReference field (labels field))
        exact ⟨by exact_mod_cast h.1,by exact_mod_cast h.2⟩
      have hDen : ∀ field, (rational field).den ≤ order ratio n epsilon := by
        intro field
        have hd := hDivides field (labels field)
        exact (Nat.le_of_dvd hPositive hd).trans hDenBound
      let code := candidateCodesOfRat ratio hr values candidateRich epsilon he rational hUnit
      have hBids : ∀ field, c.bidsA field (code field) = rational field :=
        candidateCodesOfRat_bids ratio hr values candidateRich epsilon he rational hUnit hDen
      have heq : row = fun field => (c.bidsA field (code field) : ℝ) := by
        rw [← hRow]
        funext field
        rw [hBids field]
      refine ⟨code,?_,heq⟩
      have hf := hrowFacts.2.2
      rw [heq] at hf
      change (∑ field, (c.bidsA field (code field) : ℝ)) ≤ (c.budgetA : ℝ) at hf
      change (∑ field, c.bidsA field (code field)) ≤ c.budgetA
      exact_mod_cast hf
  · change security values.values (budgets 1 : ℝ) (transportedLaw law hK coordinates) ≤
      security values.values (budgets 1 : ℝ) law + 1 / K
    rw [transportedLaw_security values.values law _ hOwn hOriginal hK budgets coordinates hCell hMargin 1]
    apply WholeQuantileRounding.roundedLaw_security_bound values.values law _ hOwn hOriginal K hK
    exact_mod_cast (normalizedInput ratio hr values candidateRich).budgetB_positive.le

/-- For EVERY actual source history, its semantic finite floor is at most
the security of an arbitrary supported original comparator plus 1/K. -/
theorem responseFloor_le_comparator {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (past : List (ProductSecurityTrainer.RawObservation (n + 1))) (hPast : 0 < past.length)
    (law : Mixed (n + 1))
    (hLaw : Supported ((normalizedInput ratio hr values candidateRich).budgetA : ℝ) law) :
    let c := trainer ratio hr values candidateRich epsilon he
    c.responseFloor past ≤ security values.values (c.budgetB : ℝ) law + 1 / quantileCount epsilon := by
  obtain ⟨comparator,_hSupported,hRows,hSecurity⟩ :=
    exists_source_comparator ratio hr values candidateRich epsilon he law hLaw
  exact ((trainer ratio hr values candidateRich epsilon he).responseFloor_le_security past hPast comparator hRows).trans hSecurity

/-- Taking the actual continuous loss infimum closes the R42 finite-floor
comparison. The strong two-security minimax identity remains separate. -/
theorem responseFloor_le_lossInfimum {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (past : List (ProductSecurityTrainer.RawObservation (n + 1))) (hPast : 0 < past.length) :
    let c := trainer ratio hr values candidateRich epsilon he
    c.responseFloor past ≤ ContinuousSecurityValues.lossInfimum values.values (c.budgetA : ℝ) (c.budgetB : ℝ) +
      1 / quantileCount epsilon := by
  let c := trainer ratio hr values candidateRich epsilon he
  have hLower : c.responseFloor past - 1 / quantileCount epsilon ≤
      ContinuousSecurityValues.lossInfimum values.values (c.budgetA : ℝ) (c.budgetB : ℝ) := by
    apply ContinuousSecurityValues.le_lossInfimum values.values (c.budgetA : ℝ) (c.budgetB : ℝ) _
      (by exact_mod_cast (normalizedInput ratio hr values candidateRich).budgetA_positive.le)
    intro law hLaw
    have h := responseFloor_le_comparator ratio hr values candidateRich epsilon he past hPast law hLaw
    change c.responseFloor past ≤ security values.values (c.budgetB : ℝ) law + 1 / quantileCount epsilon at h
    linarith
  linarith

theorem responseFloor_le_lossInfimum_epsilon {n : ℕ} (ratio : ℚ) (hr : 0 < ratio ∧ ratio ≤ 1)
    (values : RationalFieldSelector (n + 1)) (candidateRich : Bool)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (past : List (ProductSecurityTrainer.RawObservation (n + 1))) (hPast : 0 < past.length) :
    let c := trainer ratio hr values candidateRich epsilon he
    c.responseFloor past ≤ ContinuousSecurityValues.lossInfimum values.values (c.budgetA : ℝ) (c.budgetB : ℝ) +
      (epsilon : ℝ) / 64 :=
  (responseFloor_le_lossInfimum ratio hr values candidateRich epsilon he past hPast).trans
    (add_le_add le_rfl (quantile_error_le epsilon he.1))

end Blotto.WholeQuantileFareyComparator
