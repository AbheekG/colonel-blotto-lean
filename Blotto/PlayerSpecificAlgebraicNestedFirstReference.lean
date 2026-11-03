import Blotto.PlayerSpecificAlgebraicNestedFirstTable
import Blotto.RationalLotteryTranslate

/-! The actual first-table reference is the existing conditional law,
including the zero corner; every cached endpoint is feasible. -/
namespace Blotto.PlayerSpecificAlgebraicNestedFirstReference
open MeasureTheory
open PlayerSpecificAlgebraicNestedFirstTable
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem point (i : NestedInput) (htv : i.t≤ i.v) (s : ℝ) (hs : 0≤s ∧ s≤ i.t) (slot : Fin 9) (q : ℝ) :
    segmentPoint ((reference i htv s hs).P slot) ((reference i htv s hs).Q slot) q=i.firstPoint htv s slot q := by
  classical
  by_cases hp : 0 < i.conditionalProbability s
  · have hin : s∈i.positiveParameters := ⟨hs,hp⟩
    simp only [reference,dite_eq_left hp,NestedInput.firstPoint,dite_eq_left hin,ThreeGeometry.couplingPoint,
      ThreeGeometry.segmentLottery]
    exact ((AffineAllocation.shiftThird s).onSegment _ _ q).symm
  · have hin : s∉i.positiveParameters := fun h => hp h.2
    simp only [reference,dite_eq_right hp,NestedInput.firstPoint,dite_eq_right hin]

theorem at_zero (P Q : Allocation 3) : Blotto.segmentPoint P Q 0=P := by
  funext j
  simp only [Blotto.segmentPoint,sub_zero,one_mul,zero_mul,add_zero]

theorem at_one (P Q : Allocation 3) : Blotto.segmentPoint P Q 1=Q := by
  funext j
  simp only [Blotto.segmentPoint,sub_self,zero_mul,one_mul,zero_add]

theorem endpoints_budget (i : NestedInput) (htv : i.t≤ i.v) (s : ℝ) (hs : 0≤s ∧ s≤ i.t) :
    (∀ slot,FullBudget i.M ((reference i htv s hs).P slot)) ∧
      (∀ slot,FullBudget i.M ((reference i htv s hs).Q slot)) := by
  constructor
  · intro slot
    have h:=i.firstPoint_fullBudget htv hs (show (0:ℝ)≤0 ∧ (0:ℝ)≤1 by constructor <;> norm_num) slot
    rw [←point i htv s hs slot 0] at h
    rw [at_zero] at h
    exact h
  · intro slot
    have h:=i.firstPoint_fullBudget htv hs (show (0:ℝ)≤1 ∧ (1:ℝ)≤1 by constructor <;> norm_num) slot
    rw [←point i htv s hs slot 1] at h
    rw [at_one] at h
    exact h

theorem endpoints_box (i : NestedInput) (htv : i.t≤ i.v) (s : ℝ) (hs : 0≤s ∧ s≤ i.t) :
    (∀ slot,InBox ![i.a,i.d,i.c] ((reference i htv s hs).P slot)) ∧
      (∀ slot,InBox ![i.a,i.d,i.c] ((reference i htv s hs).Q slot)) := by
  constructor
  · intro slot
    have h:=i.firstPoint_inBox htv hs (show (0:ℝ)≤0 ∧ (0:ℝ)≤1 by constructor <;> norm_num) slot
    rw [←point i htv s hs slot 0] at h
    rw [at_zero] at h
    exact h
  · intro slot
    have h:=i.firstPoint_inBox htv hs (show (0:ℝ)≤1 ∧ (1:ℝ)≤1 by constructor <;> norm_num) slot
    rw [←point i htv s hs slot 1] at h
    rw [at_one] at h
    exact h

theorem law (i : NestedInput) (htv : i.t≤ i.v) (s : ℝ) (hs : 0≤s ∧ s≤ i.t) :
    ((reference i htv s hs).law : Measure (Allocation 3))=(i.firstConditionalLaw htv s : Measure (Allocation 3)) := by
  classical
  by_cases hp : 0 < i.conditionalProbability s
  · have hin : s∈i.positiveParameters := ⟨hs,hp⟩
    rw [reference,dite_eq_left hp,NestedInput.firstConditionalLaw,dite_eq_left hin]
    change (((i.firstGeometry htv s hs hp).segmentLottery.mapped (AffineAllocation.shiftThird s)).law : Measure (Allocation 3))=_
    rw [SegmentLottery.mapped_law,ThreeGeometry.segmentLottery_law]
    rfl
  · have hin : s∉i.positiveParameters := fun h => hp h.2
    rw [reference,dite_eq_right hp,NestedInput.firstConditionalLaw,dite_eq_right hin]
    simp [SegmentLottery.law,probabilityMixture,mixtureMeasure,Measure.sum_fintype,Fin.sum_univ_succ,NestedInput.firstZeroLaw]

end Blotto.PlayerSpecificAlgebraicNestedFirstReference
