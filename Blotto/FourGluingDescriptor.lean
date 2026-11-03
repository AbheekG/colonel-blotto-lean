import Blotto.FourGluing
import Blotto.OverlapBudget

/-! A compact finite segment implementation of the exact conditional gluing.
For each source pair, adjacent refinement pieces combine into one overlap
segment. The count is at most 49, hence satisfies the manuscript's 735 bound. -/

namespace Blotto.FourInput
open MeasureTheory Set

noncomputable def overlapData (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : OverlapGluing 9 9 where
  first := (i.gluingFirstSpec hcase).segmentLottery
  second := (i.gluingSecondSpec hcase).segmentLottery
  firstProbe := AffineProbe.coordinate 2
  secondProbe := AffineProbe.reflectedCoordinate i.auxLength 0
  d := i.auxLength
  d_pos := i.auxLength_pos
  first_uniform := (i.gluingData hcase).first_uniform
  second_uniform := by
    rw [(i.gluingSecondSpec hcase).segmentLottery_law]
    exact (i.gluingData hcase).second_uniform
  first_P_range := (i.gluingData hcase).first_P_range
  first_Q_range := (i.gluingData hcase).first_Q_range

theorem overlap_allocation_law (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    ((i.overlapData hcase).auxiliary.allocationLaw : Measure (Allocation 4)) =
      (i.gluingCaseLaw hcase : Measure (Allocation 4)) := by
  change Measure.map glueAllocation (i.overlapData hcase).auxiliary.rawLaw =
    Measure.map glueAllocation (i.gluingData hcase).rawLaw
  unfold AuxiliaryGluing.rawLaw AuxiliaryGluing.pairedPoint AuxiliaryGluing.cell
  simp only [OverlapGluing.auxiliary, overlapData, gluingData]
  rw [(i.gluingSecondSpec hcase).segmentLottery_law]

noncomputable def gluingDescriptor (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : SegmentLottery 4 81 :=
  (i.overlapData hcase).descriptor i.B

theorem gluingDescriptor_law (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    ((i.gluingDescriptor hcase).law : Measure (Allocation 4)) = (i.gluingCaseLaw hcase : Measure (Allocation 4)) :=
  ((i.overlapData hcase).descriptor_law i.B).trans (i.overlap_allocation_law hcase)

theorem gluingDescriptor_positive (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    (i.gluingDescriptor hcase).positiveSlots.card ≤ 49 := by
  have he := (i.overlapData hcase).descriptor_positive_bound i.B
  have hA := (i.gluingFirstSpec hcase).segmentLottery_positive
  have hB := (i.gluingSecondSpec hcase).segmentLottery_positive
  exact he.trans (Nat.mul_le_mul hA hB)

theorem gluingDescriptor_paper_bound (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    (i.gluingDescriptor hcase).positiveSlots.card ≤ 735 :=
  (i.gluingDescriptor_positive hcase).trans (by decide)

theorem gluingDescriptor_endpoints (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    (∀ r, FullBudget i.B ((i.gluingDescriptor hcase).P r)) ∧
      (∀ r, FullBudget i.B ((i.gluingDescriptor hcase).Q r)) := by
  have hA := (i.gluingFirstSpec hcase).segmentLottery_endpoints
  have hB := (i.gluingSecondSpec hcase).segmentLottery_endpoints
  have hsum : (i.gluingFirstSpec hcase).B + (i.gluingSecondSpec hcase).B - (i.overlapData hcase).d = i.B :=
    i.auxiliary_budget_sum
  have he := (i.overlapData hcase).descriptor_endpoints hA.1 hA.2 hB.1 hB.2 rfl rfl
    (by simpa only [hsum] using (le_of_lt i.lengths_positive.2.2.1))
  simpa only [gluingDescriptor, hsum] using he

theorem gluingDescriptor_point_fullBudget (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w)
    (index : Fin 81) {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    FullBudget i.B ((i.gluingDescriptor hcase).point index t) :=
  (i.gluingDescriptor hcase).point_fullBudget (i.gluingDescriptor_endpoints hcase).1
    (i.gluingDescriptor_endpoints hcase).2 index ht

/-- Both branches now have concrete output paths with a hard-budget proof. -/
noncomputable def point (i : FourInput) (useUniform : Bool) (choice : ℕ → Bool) (useFamily : Bool)
    (r t : ℝ) (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) : Allocation 4 :=
  if hcase : (1 - i.p) * i.ell ≤ i.w then (i.gluingDescriptor hcase).point index t else
    i.smallCasePoint (lt_of_not_ge hcase) useUniform choice useFamily r t edge residualEdge

theorem point_fullBudget (i : FourInput) (useUniform : Bool) (choice : ℕ → Bool) (useFamily : Bool)
    {r t : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) :
    FullBudget i.B (i.point useUniform choice useFamily r t index edge residualEdge) := by
  unfold point
  split_ifs with hcase
  · exact i.gluingDescriptor_point_fullBudget hcase index ht
  · exact i.smallCasePoint_fullBudget (lt_of_not_ge hcase) useUniform choice useFamily hr ht edge residualEdge

theorem law_supported (i : FourInput) : Supported i.B i.law :=
  i.coupling_contract.1.mono fun _ hx => ⟨hx.1, le_of_eq hx.2⟩

end Blotto.FourInput

namespace Blotto
open MeasureTheory Set

/-- The complete mathematical coupling assertion of manuscript Lemma 2.4,
with both explicit constructions instantiated. Computational cost and the
finite-binary implementation remain separate obligations. -/
theorem exists_four_coupling (B u v w ell p : ℝ) (hu : 0 < u) (huv : u ≤ v) (hvw : v ≤ w)
    (hell : 0 < ell) (hp : 0 < p) (hp1 : p < 1) (hwB : w ≤ B) (hellB : ell ≤ B)
    (hmean : u + v + w + p * ell = 2 * B) :
    ∃ μ : Mixed 4, (∀ᵐ x ∂(μ : Measure (Allocation 4)), FullBudget B x) ∧
      (marginal μ 0 : Measure ℝ) = uniformLaw u ∧
      (marginal μ 1 : Measure ℝ) = uniformLaw v ∧
      (marginal μ 2 : Measure ℝ) = uniformLaw w ∧
      (marginal μ 3 : Measure ℝ) = zeroUniformLaw ell p := by
  let i : FourInput := ⟨B, u, v, w, ell, p, hu, huv, hvw, hell, hp, hp1, hwB, hellB, hmean⟩
  exact ⟨i.law, i.coupling_contract⟩

end Blotto
