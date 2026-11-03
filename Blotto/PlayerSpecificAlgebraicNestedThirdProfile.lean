import Blotto.PlayerSpecificAlgebraicNestedProfileTransport

/-! Actual third nested profile. The v=0 branch omits the undefined
family and retains a padded residual descriptor with feasible endpoints. -/
namespace Blotto.PlayerSpecificAlgebraicNestedThirdProfile
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes
open PlayerSpecificAlgebraicDescriptorReference PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def positive (model : RationalCostModel) (root : Candidate) (p : Prepared) : Bool :=
  !PlayerSpecificAlgebraicPairStep.le model root p.v []

def residual (model : RationalCostModel) (root : Candidate) (a : Input) : Descriptor 3 9 :=
  PlayerSpecificAlgebraicDescriptorPad.pad (PlayerSpecificAlgebraicResidualTable.prepare model root a) 6 0

def prepare (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (K : ℕ) (outer : Fin K → Bool) :
    Descriptor 3 18 :=
  let r := residual model root a
  if positive model root p then PlayerSpecificAlgebraicDescriptorBinary.binary root p.thirdAlpha
    (PlayerSpecificAlgebraicNestedFamily.profile model root a p.v K outer) r
  else PlayerSpecificAlgebraicDescriptorPad.pad r 9 0

noncomputable def residualReference (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) : SegmentLottery 3 9 :=
  PlayerSpecificSegmentAssemblyReference.pad (i.residualInput hvt htu).segmentLottery 6 0

noncomputable def reference (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ) (outer : Fin K → Bool) :
    SegmentLottery 3 18 := by
  classical
  exact if hv : 0 < i.v then PlayerSpecificSegmentAssemblyReference.binary i.thirdAlpha
    ⟨(i.thirdAlpha_bounds hv hvt).1.le,(i.thirdAlpha_bounds hv hvt).2.le⟩
    (PlayerSpecificAlgebraicNestedFamilyReference.reference i i.v hv le_rfl K outer) (residualReference i hvt htu)
  else PlayerSpecificSegmentAssemblyReference.pad (residualReference i hvt htu) 9 0

theorem positive_correct (model : RationalCostModel) (root : Candidate) (p : Prepared) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (hp : PlayerSpecificAlgebraicNestedCaseParameters.Values p i x) :
    positive model root p=true ↔ 0 < i.v := by
  have hz : realEvaluate [] x=0 := rfl
  simp only [positive,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,
    PlayerSpecificAlgebraicPairStep.le_correct model root _ _ hm hirr hv x hx,not_le,hp.v,hz]

theorem refines (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (hp : PlayerSpecificAlgebraicNestedCaseParameters.Values p i x)
    (T : ℕ) (hfit : Fits root a T) (hpb : PlayerSpecificAlgebraicNestedCaseParameters.Bounds root p T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T)
    (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ) (outer : Fin K → Bool) :
    Refines (prepare model root a p K outer) x (reference i hvt htu K outer) := by
  have hr := PlayerSpecificAlgebraicDescriptorPad.refines (PlayerSpecificAlgebraicResidualTable.prepare model root a) 6 0 x
    (i.residualInput hvt htu).segmentLottery
    (PlayerSpecificAlgebraicResidualTable.refines model root a i hm hirr hv x hx ha T hfit hml hmT hvt htu)
  have hc := positive_correct model root p i hm hirr hv x hx hp
  by_cases hv0 : 0 < i.v
  · rw [prepare,ite_eq_left (hc.mpr hv0),reference,dite_eq_left hv0]
    exact PlayerSpecificAlgebraicNestedProfileTransport.binary_refines root p.thirdAlpha _ _ x hx.1 i.thirdAlpha
      ⟨(i.thirdAlpha_bounds hv0 hvt).1.le,(i.thirdAlpha_bounds hv0 hvt).2.le⟩ hp.thirdAlpha _ _
      (PlayerSpecificAlgebraicNestedProfileTransport.family_refines model root a i hm hirr hv x hx ha p.v T
        hfit hpb.v hml hmT hT i.v hv0 le_rfl hp.v K outer) hr
  · rw [prepare,ite_eq_right (fun h => hv0 (hc.mp h)),reference,dite_eq_right hv0]
    exact PlayerSpecificAlgebraicDescriptorPad.refines (residual model root a) 9 0 x (residualReference i hvt htu) hr

end Blotto.PlayerSpecificAlgebraicNestedThirdProfile
