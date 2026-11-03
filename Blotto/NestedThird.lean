import Blotto.NestedThirdIdentity

/-! The middle nested case: F_v's first-case coupling plus the explicit
three-segment residual. For v=0 only the residual is used. -/

namespace Blotto.NestedInput
open MeasureTheory Set

noncomputable def thirdLaw (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) : Mixed 3 :=
  if hv : 0 < i.v then
    binaryLaw i.thirdAlpha ⟨le_of_lt (i.thirdAlpha_bounds hv hvt).1,
      le_of_lt (i.thirdAlpha_bounds hv hvt).2⟩
      (i.familyFirstLaw i.v hv le_rfl) (i.residualInput hvt htu).law
  else (i.residualInput hvt htu).law

theorem third_residual_contract (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) :
    (∀ᵐ x ∂((i.residualInput hvt htu).law : Measure (Allocation 3)), FullBudget i.M x) ∧
    (marginal (i.residualInput hvt htu).law 0 : Measure ℝ) = uniformLaw i.a ∧
    (marginal (i.residualInput hvt htu).law 1 : Measure ℝ) = uniformLaw i.d ∧
    (marginal (i.residualInput hvt htu).law 2 : Measure ℝ) = (i.residualInput hvt htu).targetLaw := by
  have he := i.geometry_matches
  simpa only [residualInput, he.1, he.2.1, he.2.2.2] using (i.residualInput hvt htu).coupling_contract

theorem third_coupling_contract (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) :
    (∀ᵐ x ∂(i.thirdLaw hvt htu : Measure (Allocation 3)), FullBudget i.M x) ∧
      (marginal (i.thirdLaw hvt htu) 0 : Measure ℝ) = uniformLaw i.a ∧
      (marginal (i.thirdLaw hvt htu) 1 : Measure ℝ) = uniformLaw i.d ∧
      (marginal (i.thirdLaw hvt htu) 2 : Measure ℝ) = i.nestedTargetLaw := by
  have hr := i.third_residual_contract hvt htu
  unfold thirdLaw
  split_ifs with hv
  · have hf := i.familyFirstLaw_contract i.v hv le_rfl
    refine ⟨binaryLaw_fullBudget _ _ _ _ hf.1 hr.1, ?_, ?_, ?_⟩
    · exact binaryLaw_marginal_common _ _ _ _ 0 _ hf.2.1 hr.2.1
    · exact binaryLaw_marginal_common _ _ _ _ 1 _ hf.2.2.1 hr.2.2.1
    · rw [binaryLaw_marginal, hf.2.2.2, hr.2.2.2]
      exact (i.third_decomposition hv hvt htu).symm
  · have hv0 : i.v = 0 := le_antisymm (le_of_not_gt hv) i.lengths.1
    refine ⟨hr.1, hr.2.1, hr.2.2.1, ?_⟩
    rw [hr.2.2.2, i.residual_zero_target hv0 hvt htu]

noncomputable def thirdPoint (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u)
    (useFamily : Bool) (r t : ℝ) (edge : Fin 9) (residualEdge : Fin 3) : Allocation 3 :=
  if hv : 0 < i.v then
    if useFamily then i.familyFirstPoint i.v hv le_rfl r edge t else
      segmentPoint ((i.residualInput hvt htu).vertex (NestedResidual.edges residualEdge).1)
        ((i.residualInput hvt htu).vertex (NestedResidual.edges residualEdge).2) t
  else segmentPoint ((i.residualInput hvt htu).vertex (NestedResidual.edges residualEdge).1)
    ((i.residualInput hvt htu).vertex (NestedResidual.edges residualEdge).2) t

theorem thirdPoint_fullBudget (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u)
    (useFamily : Bool) {r t : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (edge : Fin 9) (residualEdge : Fin 3) :
    FullBudget i.M (i.thirdPoint hvt htu useFamily r t edge residualEdge) := by
  have hB : (i.residualInput hvt htu).g.budget = i.M := i.geometry_matches.2.2.2
  unfold thirdPoint
  split_ifs with hv hFamily
  · exact i.familyFirstPoint_fullBudget _ _ _ hr ht edge
  · simpa only [hB] using (i.residualInput hvt htu).pointwise_fullBudget residualEdge ht
  · simpa only [hB] using (i.residualInput hvt htu).pointwise_fullBudget residualEdge ht

end Blotto.NestedInput
