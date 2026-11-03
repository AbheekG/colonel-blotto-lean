import Blotto.NestedSecond
import Blotto.NestedThird

/-! Assembles all three nested-uniform cases into an actual joint law.
This closes the mathematical assertion of Lemma 2.3; computational contracts
and finite-bit approximation remain separate obligations. -/

namespace Blotto.NestedInput
open MeasureTheory Set

noncomputable def couplingLaw (i : NestedInput) : Mixed 3 :=
  if htv : i.t ≤ i.v then i.firstLaw htv else
    if htu : i.u ≤ i.t then i.secondLaw htu else
      i.thirdLaw (lt_of_not_ge htv) (lt_of_not_ge htu)

theorem coupling_contract (i : NestedInput) :
    (∀ᵐ x ∂(i.couplingLaw : Measure (Allocation 3)), FullBudget i.M x) ∧
      (marginal i.couplingLaw 0 : Measure ℝ) = uniformLaw i.a ∧
      (marginal i.couplingLaw 1 : Measure ℝ) = uniformLaw i.d ∧
      (marginal i.couplingLaw 2 : Measure ℝ) = i.nestedTargetLaw := by
  unfold couplingLaw
  split_ifs with htv htu
  · exact i.first_coupling_contract htv
  · exact i.second_coupling_contract htu
  · exact i.third_coupling_contract (lt_of_not_ge htv) (lt_of_not_ge htu)

theorem couplingLaw_supported (i : NestedInput) : Supported i.M i.couplingLaw :=
  i.coupling_contract.1.mono fun _ hx => ⟨hx.1, le_of_eq hx.2⟩

theorem exists_coupling (i : NestedInput) :
    ∃ μ : Mixed 3, (∀ᵐ x ∂(μ : Measure (Allocation 3)), FullBudget i.M x) ∧
      (marginal μ 0 : Measure ℝ) = uniformLaw i.a ∧
      (marginal μ 1 : Measure ℝ) = uniformLaw i.d ∧
      (marginal μ 2 : Measure ℝ) = i.nestedTargetLaw :=
  ⟨i.couplingLaw, i.coupling_contract⟩

/-- The output path of the assembled three-case construction. -/
noncomputable def couplingPoint (i : NestedInput) (useFamily : Bool) (r t : ℝ)
    (edge : Fin 9) (residualEdge : Fin 3) : Allocation 3 :=
  if htv : i.t ≤ i.v then i.firstPoint htv (i.location r) edge t else
    if htu : i.u ≤ i.t then i.secondPoint htu useFamily r t edge else
      i.thirdPoint (lt_of_not_ge htv) (lt_of_not_ge htu) useFamily r t edge residualEdge

theorem couplingPoint_fullBudget (i : NestedInput) (useFamily : Bool) {r t : ℝ}
    (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) (edge : Fin 9) (residualEdge : Fin 3) :
    FullBudget i.M (i.couplingPoint useFamily r t edge residualEdge) := by
  unfold couplingPoint
  split_ifs with htv htu
  · exact i.firstSamplePath_fullBudget htv hr ht edge
  · exact i.secondPoint_fullBudget htu useFamily hr ht edge
  · exact i.thirdPoint_fullBudget (lt_of_not_ge htv) (lt_of_not_ge htu) useFamily hr ht edge residualEdge

end Blotto.NestedInput

namespace Blotto
open MeasureTheory Set

/-- The full mathematical assertion of manuscript Lemma 2.3, without the
coordinate ordering convention. All three component laws are constructed. -/
theorem exists_nested_coupling (M a d c t q : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hc : 0 < c) (ht : 0 < t) (htc : t < c)
    (hq : 0 < q) (hq1 : q < 1) (haM : a ≤ M) (hdM : d ≤ M) (hcM : c ≤ M)
    (hbalance : a + d + q * t + (1 - q) * c = 2 * M) :
    ∃ μ : Mixed 3, (∀ᵐ x ∂(μ : Measure (Allocation 3)), FullBudget M x) ∧
      (marginal μ 0 : Measure ℝ) = uniformLaw a ∧
      (marginal μ 1 : Measure ℝ) = uniformLaw d ∧
      (marginal μ 2 : Measure ℝ) =
        ENNReal.ofReal q • uniformLaw t + ENNReal.ofReal (1 - q) • uniformLaw c := by
  by_cases had : a ≤ d
  · let i : NestedInput := ⟨M, a, d, c, t, q, ha, hd, hc, ht, htc, hq, hq1, haM, hdM, hcM, had, hbalance⟩
    exact i.exists_coupling
  · let i : NestedInput := ⟨M, d, a, c, t, q, hd, ha, hc, ht, htc, hq, hq1, hdM, haM, hcM,
      le_of_lt (lt_of_not_ge had), by linarith⟩
    rcases i.exists_coupling with ⟨μ, hμ, h0, h1, h2⟩
    refine ⟨swapLaw μ, swapLaw_fullBudget hμ, ?_, ?_, ?_⟩
    · simpa [swapLaw_marginal, swapIndex] using h1
    · simpa [swapLaw_marginal, swapIndex] using h0
    · simpa [swapLaw_marginal, swapIndex, NestedInput.nestedTargetLaw] using h2

end Blotto
