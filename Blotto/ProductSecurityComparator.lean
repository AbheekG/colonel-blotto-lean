import Blotto.ProductSecurityHistoryLaws

/-! A finite security floor is below the actual continuous security of ANY
whole law supported on feasible candidate code rows. Comparator masses may
be arbitrary real probabilities; no rational-weight conversion is assumed. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators Classical

theorem RationalWholeRowLaw.one_sub_purePayoff {r m : ℕ} (law : RationalWholeRowLaw r m)
    (values : Values m) (candidate : Allocation m) :
    1 - purePayoff values candidate law.law =
      ∑ i, law.realWeight i * payoff values (law.realRow i) candidate := by
  rw [law.purePayoff_eq_sum,← law.realWeight_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hc := payoff_constant_sum values candidate (law.realRow i)
  have he : payoff values (law.realRow i) candidate = 1 - payoff values candidate (law.realRow i) := by linarith
  rw [he]
  ring

namespace ProductSecurityTrainer

theorem responseFloor_le_one_sub_payoff {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length)
    (code : SparseMW.ProductCodes c.sizesA)
    (hCode : SparseMW.productResource c.bidsA code ≤ c.budgetA) :
    c.responseFloor past ≤ 1 - purePayoff c.values.values
      (fun field => (c.bidsA field (code field) : ℝ)) (c.averageLawB past hPast).law := by
  let label : Fin c.actionsA := (SparseMW.feasibleEquiv c.bidsA c.budgetA) ⟨code,hCode⟩
  have hLabel : c.codeA label = code := by
    change ((SparseMW.feasibleEquiv c.bidsA c.budgetA).symm
      ((SparseMW.feasibleEquiv c.bidsA c.budgetA) ⟨code,hCode⟩)).val = code
    rw [Equiv.symm_apply_apply]
  have hm := FiniteSaddle.minimizingRow_le c.actionsA_positive c.matrix
    (rawHistoryAverage (fun h => (c.rawLawB h).realWeight) past) label
  change c.responseFloor past ≤ _ at hm
  apply hm.trans_eq
  rw [RationalWholeRowLaw.one_sub_purePayoff,averageLawB_realWeight]
  unfold FiniteSaddle.RowLoss
  apply Finset.sum_congr rfl
  intro j _
  change payoff c.values.values (fun field => (c.bidsB field (c.codeB j field) : ℝ))
    (fun field => (c.bidsA field (c.codeA label field) : ℝ)) * _ =
    _ * payoff c.values.values (fun field => (c.bidsB field (c.codeB j field) : ℝ))
      (fun field => (c.bidsA field (code field) : ℝ))
  rw [hLabel,mul_comm]

/-- A semantic floor comparison with the actual continuous supremum.
Whole-law probabilities can be real; feasibility and membership are almost
sure properties of the comparator's complete allocation rows. -/
theorem responseFloor_le_security {m : ℕ} (c : ProductSecurityTrainer m)
    (past : List (RawObservation m)) (hPast : 0 < past.length) (law : Mixed m)
    (hRows : ∀ᵐ row ∂(law : Measure (Allocation m)),
      ∃ code : SparseMW.ProductCodes c.sizesA,
        SparseMW.productResource c.bidsA code ≤ c.budgetA ∧
        row = fun field => (c.bidsA field (code field) : ℝ)) :
    c.responseFloor past ≤ security c.values.values (c.budgetB : ℝ) law := by
  have hPointwise : ∀ᵐ row ∂(law : Measure (Allocation m)),
      purePayoff c.values.values row (c.averageLawB past hPast).law ≤ 1 - c.responseFloor past :=
    hRows.mono fun row hr => by
      obtain ⟨code,hCode,rfl⟩ := hr
      have h := c.responseFloor_le_one_sub_payoff past hPast code hCode
      linarith
  have hIntegral := integral_mono_ae
    (integrable_purePayoff c.values.values law (c.averageLawB past hPast).law)
    (integrable_const (1 - c.responseFloor past)) hPointwise
  have hExpected : expected c.values.values law (c.averageLawB past hPast).law ≤
      1 - c.responseFloor past := by
    rw [expected_iterated]
    simpa using hIntegral
  have hSum := expected_constant_sum c.values.values law (c.averageLawB past hPast).law
  have hSecurity := expected_le_security c.values.values (c.averageLawB past hPast).law law
    (c.averageLawB_supported past hPast)
  linarith

end ProductSecurityTrainer
end Blotto
