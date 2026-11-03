import Blotto.FourReflectionRecovery
import Blotto.ThreeLottery
import Blotto.GluingBudget

/-! Actual four-variable law in the auxiliary-gluing case. Its finite segment
implementation is constructed separately from this conditional measure proof. -/

namespace Blotto.FourInput
open MeasureTheory Set

noncomputable def gluingFirstSpec (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : ThreeSpec where
  B := i.firstBudget
  a := i.u
  d := i.v
  c := i.auxLength
  p := 1
  B_pos := (i.auxiliary_budget_bounds hcase).1
  a_pos := i.u_pos
  d_pos := i.lengths_positive.1
  c_pos := i.auxLength_pos
  p_pos := by norm_num
  a_le := (i.auxiliary_budget_bounds hcase).2.1
  d_le := (i.auxiliary_budget_bounds hcase).2.2.1
  c_le := (i.auxiliary_budget_bounds hcase).2.2.2.1
  p_le := le_rfl
  balance := by dsimp [firstBudget]; ring

noncomputable def gluingSecondSpec (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : ThreeSpec where
  B := i.secondBudget
  a := i.auxLength
  d := i.w
  c := i.ell
  p := i.p
  B_pos := (i.auxiliary_budget_bounds hcase).2.2.2.2.1
  a_pos := i.auxLength_pos
  d_pos := i.lengths_positive.2.1
  c_pos := i.ell_pos
  p_pos := i.p_pos
  a_le := (i.auxiliary_budget_bounds hcase).2.2.2.2.2.1
  d_le := (i.auxiliary_budget_bounds hcase).2.2.2.2.2.2.1
  c_le := (i.auxiliary_budget_bounds hcase).2.2.2.2.2.2.2
  p_le := le_of_lt i.p_lt
  balance := by dsimp [secondBudget]; ring

noncomputable def gluingData (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : AuxiliaryGluing 3 3 9 where
  first := (i.gluingFirstSpec hcase).segmentLottery
  second := (i.gluingSecondSpec hcase).law
  firstProbe := AffineProbe.coordinate 2
  secondProbe := AffineProbe.reflectedCoordinate i.auxLength 0
  d := i.auxLength
  d_pos := i.auxLength_pos
  first_uniform := by
    change Measure.map (fun x : Allocation 3 => x 2) ((i.gluingFirstSpec hcase).segmentLottery.law : Measure (Allocation 3)) = _
    rw [(i.gluingFirstSpec hcase).segmentLottery_law]
    have h := (i.gluingFirstSpec hcase).law_contract.2.2.2
    change Measure.map (fun x : Allocation 3 => x 2) ((i.gluingFirstSpec hcase).law : Measure (Allocation 3)) =
      zeroUniformLaw i.auxLength 1 at h
    simpa [gluingFirstSpec, zeroUniformLaw] using h
  second_uniform := by
    change Measure.map (fun x : Allocation 3 => i.auxLength - x 0) ((i.gluingSecondSpec hcase).law : Measure (Allocation 3)) = _
    have he : (fun x : Allocation 3 => i.auxLength - x 0) =
        (fun z : ℝ => i.auxLength - z) ∘ (fun x : Allocation 3 => x 0) := rfl
    rw [he, ← Measure.map_map (g := fun z : ℝ => i.auxLength - z)
      (measurable_const.sub measurable_id) (measurable_pi_apply 0)]
    have hm : (marginal (i.gluingSecondSpec hcase).law 0 : Measure ℝ) = uniformLaw i.auxLength :=
      (i.gluingSecondSpec hcase).law_contract.2.1
    change Measure.map (fun z => i.auxLength - z) (marginal (i.gluingSecondSpec hcase).law 0 : Measure ℝ) = _
    rw [hm, reflect_uniformLaw i.auxLength_pos, sub_self, affineUniform_zero_uniformLaw i.auxLength_pos]
  first_P_range := fun j => (i.gluingFirstSpec hcase).segmentLottery_box.1 j 2
  first_Q_range := fun j => (i.gluingFirstSpec hcase).segmentLottery_box.2 j 2

noncomputable def gluingCaseLaw (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : Mixed 4 :=
  (i.gluingData hcase).allocationLaw

theorem gluingCaseLaw_contract (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    (∀ᵐ x ∂(i.gluingCaseLaw hcase : Measure (Allocation 4)), FullBudget i.B x) ∧
      (marginal (i.gluingCaseLaw hcase) 0 : Measure ℝ) = uniformLaw i.u ∧
      (marginal (i.gluingCaseLaw hcase) 1 : Measure ℝ) = uniformLaw i.v ∧
      (marginal (i.gluingCaseLaw hcase) 2 : Measure ℝ) = uniformLaw i.w ∧
      (marginal (i.gluingCaseLaw hcase) 3 : Measure ℝ) = zeroUniformLaw i.ell i.p := by
  unfold gluingCaseLaw
  have hA := (i.gluingFirstSpec hcase).segmentLottery_endpoints
  have hB := (i.gluingSecondSpec hcase).law_contract
  have h := (i.gluingData hcase).allocationLaw_fullBudget hA.1 hA.2 hB.1 rfl rfl
  have hm := (i.gluingData hcase).allocationLaw_marginals
  have hM := (i.gluingFirstSpec hcase).law_contract
  constructor
  · have he : (i.gluingFirstSpec hcase).B + (i.gluingSecondSpec hcase).B - (i.gluingData hcase).d = i.B :=
      i.auxiliary_budget_sum
    simpa only [he] using h
  constructor
  · rw [hm.1]
    change (marginal (i.gluingFirstSpec hcase).segmentLottery.law 0 : Measure ℝ) = _
    have he := (i.gluingFirstSpec hcase).segmentLottery_law
    have hn := congrArg (Measure.map (fun x : Allocation 3 => x 0)) he
    change (marginal (i.gluingFirstSpec hcase).segmentLottery.law 0 : Measure ℝ) =
      (marginal (i.gluingFirstSpec hcase).law 0 : Measure ℝ) at hn
    exact hn.trans hM.2.1
  constructor
  · rw [hm.2.1]
    have he := congrArg (Measure.map (fun x : Allocation 3 => x 1)) (i.gluingFirstSpec hcase).segmentLottery_law
    exact he.trans hM.2.2.1
  constructor
  · rw [hm.2.2.1]
    exact hB.2.2.1
  · rw [hm.2.2.2]
    exact hB.2.2.2

noncomputable def law (i : FourInput) : Mixed 4 :=
  if hcase : (1 - i.p) * i.ell ≤ i.w then i.gluingCaseLaw hcase else i.smallCaseLaw (lt_of_not_ge hcase)

theorem coupling_contract (i : FourInput) :
    (∀ᵐ x ∂(i.law : Measure (Allocation 4)), FullBudget i.B x) ∧
      (marginal i.law 0 : Measure ℝ) = uniformLaw i.u ∧
      (marginal i.law 1 : Measure ℝ) = uniformLaw i.v ∧
      (marginal i.law 2 : Measure ℝ) = uniformLaw i.w ∧
      (marginal i.law 3 : Measure ℝ) = zeroUniformLaw i.ell i.p := by
  unfold law
  split_ifs with hcase
  · exact i.gluingCaseLaw_contract hcase
  · exact i.smallCaseLaw_contract (lt_of_not_ge hcase)

end Blotto.FourInput
