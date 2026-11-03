import Blotto.PlayerSpecificAlgebraicThreeInput

/-! Actual ordered three-variable descriptor preparation, including the
forced exceptional E=0 branch. The real witness never enters execution. -/
namespace Blotto.PlayerSpecificAlgebraicOrderedThree
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicThreeInput
open PlayerSpecificAlgebraicCandidates (Candidate)
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def exceptional (root : Candidate) (a : Input) : Descriptor 3 9 :=
  ⟨FixedArrayTable.ofFn (fun slot => PlayerSpecificAlgebraicField.constant root.polynomial (if slot=0 then 1 else 0)),
    FixedArrayTable.ofFn (fun _ => FixedArrayTable.ofFn ![[],[],a.budget]),
    FixedArrayTable.ofFn (fun _ => FixedArrayTable.ofFn ![a.first,a.second,[]])⟩

def prepare (model : RationalCostModel) (root : Candidate) (a : Input) : Descriptor 3 9 :=
  if positive model root a then PlayerSpecificAlgebraicThreeGeometry.prepare model root (environment root a)
  else exceptional root a

theorem fields (model : RationalCostModel) (root : Candidate) (a : Input) (i : ThreeInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) (ha : PlayerSpecificAlgebraicThreeInput.Values a i x) :
    (∀ slot,realEvaluate ((prepare model root a).weights.read slot) x=i.segmentLottery.weight slot) ∧
      (∀ slot j,realEvaluate (((prepare model root a).first.read slot).read j) x=i.segmentLottery.P slot j) ∧
      (∀ slot j,realEvaluate (((prepare model root a).second.read slot).read j) x=i.segmentLottery.Q slot j) := by
  have hm0 : root.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hc:=positive_correct model root a i hm hirr hv x hx ha
  by_cases hE : 0 < i.a+i.d-i.B
  · rw [prepare,ite_eq_left (hc.mpr hE)]
    have hfields:=PlayerSpecificAlgebraicThreeGeometry.fields model root (environment root a) hm hirr hv x hx
      (environment_reduced root a hm hm0) (i.geometry hE) (environment_value root a i x hx.1 ha hE)
    simpa only [ThreeInput.segmentLottery,dite_eq_left hE,ThreeGeometry.segmentLottery,RationalThreeGeometry.edges_real] using hfields
  · rw [prepare,ite_eq_right (fun h => hE (hc.mp h))]
    refine ⟨?_,?_,?_⟩
    · intro slot
      by_cases hs : slot=0 <;> simp [exceptional,FixedArrayTable.read_ofFn,hs,
        PlayerSpecificAlgebraicField.constant_value _ _ x hx.1,ThreeInput.segmentLottery,hE]
    · intro slot j
      have hz : realEvaluate [] x=0 := rfl
      fin_cases j <;> simp [exceptional,FixedArrayTable.read_ofFn,ThreeInput.segmentLottery,hE,
        hz,ha.budget]
    · intro slot j
      have hz : realEvaluate [] x=0 := rfl
      fin_cases j <;> simp [exceptional,FixedArrayTable.read_ofFn,ThreeInput.segmentLottery,hE,
        hz,ha.first,ha.second]

end Blotto.PlayerSpecificAlgebraicOrderedThree
