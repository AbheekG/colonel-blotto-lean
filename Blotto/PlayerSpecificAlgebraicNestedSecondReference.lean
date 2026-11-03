import Blotto.PlayerSpecificAlgebraicNestedSecondUniform

/-! The shifted uniform component has exactly the paper's reference law.
Every stored endpoint, including unused slots, satisfies its budget and box. -/
namespace Blotto.PlayerSpecificAlgebraicNestedSecondReference
open MeasureTheory
open PlayerSpecificAlgebraicNestedSecondUniform
set_option autoImplicit false

theorem law (i : NestedInput) (htu : i.u ≤ i.t) (hmir : i.mirrorLength < i.t) :
    ((reference i htu hmir).law : Measure (Allocation 3)) = i.secondUniformLaw htu hmir := by
  rw [reference,SegmentLottery.mapped_law,(i.secondUniformInput htu hmir).segmentLottery_law]
  rfl

theorem endpoints_budget (i : NestedInput) (htu : i.u ≤ i.t) (hmir : i.mirrorLength < i.t) :
    (∀ slot,FullBudget i.M ((reference i htu hmir).P slot)) ∧
      (∀ slot,FullBudget i.M ((reference i htu hmir).Q slot)) := by
  have hs := (i.mirrorLength_bounds htu).1.le
  have he := (i.secondUniformInput htu hmir).segmentLottery_endpoints
  have hb : (i.secondUniformInput htu hmir).B + i.mirrorLength = i.M := by
    dsimp [NestedInput.secondUniformInput]
    ring
  constructor
  · intro slot
    change FullBudget i.M (shiftThird i.mirrorLength ((i.secondUniformInput htu hmir).segmentLottery.P slot))
    simpa only [hb] using shiftThird_fullBudget hs (he.1 slot)
  · intro slot
    change FullBudget i.M (shiftThird i.mirrorLength ((i.secondUniformInput htu hmir).segmentLottery.Q slot))
    simpa only [hb] using shiftThird_fullBudget hs (he.2 slot)

theorem endpoints_box (i : NestedInput) (htu : i.u ≤ i.t) (hmir : i.mirrorLength < i.t) :
    (∀ slot,InBox ![i.a,i.d,i.c] ((reference i htu hmir).P slot)) ∧
      (∀ slot,InBox ![i.a,i.d,i.c] ((reference i htu hmir).Q slot)) := by
  have hs := (i.mirrorLength_bounds htu).1.le
  have he := (i.secondUniformInput htu hmir).segmentLottery_box
  have transfer : ∀ y,InBox ![i.a,i.d,i.t-i.mirrorLength] y →
      InBox ![i.a,i.d,i.c] (shiftThird i.mirrorLength y) := by
    intro y hy
    have hb : InBox ![i.a,i.d,i.t] (shiftThird i.mirrorLength y) := by
      simpa only [sub_add_cancel] using shiftThird_inBox hs hy
    apply inBox_mono _ hb
    intro j
    fin_cases j
    · exact le_rfl
    · exact le_rfl
    · exact i.t_lt.le
  exact ⟨fun slot => transfer _ (he.1 slot),fun slot => transfer _ (he.2 slot)⟩

end Blotto.PlayerSpecificAlgebraicNestedSecondReference
