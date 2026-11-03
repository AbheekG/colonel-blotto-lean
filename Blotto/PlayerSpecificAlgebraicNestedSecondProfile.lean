import Blotto.PlayerSpecificAlgebraicNestedThirdProfile

/-! Actual second nested profile. A strict mirror-length comparison
prevents constructing a uniform component on a zero-length interval. -/
namespace Blotto.PlayerSpecificAlgebraicNestedSecondProfile
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes
open PlayerSpecificAlgebraicDescriptorReference PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def strict (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) : Bool :=
  !PlayerSpecificAlgebraicPairStep.le model root a.short p.mirror

def prepare (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (K : ℕ) (outer : Fin K → Bool) :
    Descriptor 3 18 :=
  let f := PlayerSpecificAlgebraicNestedFamily.profile model root a p.mirror K outer
  if strict model root a p then PlayerSpecificAlgebraicDescriptorBinary.binary root p.secondAlpha f
    (PlayerSpecificAlgebraicNestedSecondUniform.prepare model root a p)
  else PlayerSpecificAlgebraicDescriptorPad.pad f 9 0

noncomputable def reference (i : NestedInput) (htu : i.u ≤ i.t) (K : ℕ) (outer : Fin K → Bool) : SegmentLottery 3 18 := by
  classical
  let f := PlayerSpecificAlgebraicNestedFamilyReference.reference i i.mirrorLength
    (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K outer
  exact if hmir : i.mirrorLength < i.t then PlayerSpecificSegmentAssemblyReference.binary i.secondAlpha
    ⟨(i.secondAlpha_bounds htu).1.le,(i.secondAlpha_bounds htu).2⟩ f
    (PlayerSpecificAlgebraicNestedSecondUniform.reference i htu hmir)
  else PlayerSpecificSegmentAssemblyReference.pad f 9 0

theorem strict_correct (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (hp : PlayerSpecificAlgebraicNestedCaseParameters.Values p i x) :
    strict model root a p=true ↔ i.mirrorLength < i.t := by
  simp only [strict,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,
    PlayerSpecificAlgebraicPairStep.le_correct model root _ _ hm hirr hv x hx,not_le,ha.short,hp.mirror]

theorem refines (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (hp : PlayerSpecificAlgebraicNestedCaseParameters.Values p i x)
    (T : ℕ) (hfit : Fits root a T) (hpb : PlayerSpecificAlgebraicNestedCaseParameters.Bounds root p T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T)
    (htu : i.u ≤ i.t) (K : ℕ) (outer : Fin K → Bool) :
    Refines (prepare model root a p K outer) x (reference i htu K outer) := by
  have hf := PlayerSpecificAlgebraicNestedProfileTransport.family_refines model root a i hm hirr hv x hx ha p.mirror T
    hfit hpb.mirror hml hmT hT i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 hp.mirror K outer
  have hc := strict_correct model root a p i hm hirr hv x hx ha hp
  by_cases hmir : i.mirrorLength < i.t
  · rw [prepare,ite_eq_left (hc.mpr hmir),reference,dite_eq_left hmir]
    exact PlayerSpecificAlgebraicNestedProfileTransport.binary_refines root p.secondAlpha _ _ x hx.1 i.secondAlpha
      ⟨(i.secondAlpha_bounds htu).1.le,(i.secondAlpha_bounds htu).2⟩ hp.secondAlpha _ _ hf
      (PlayerSpecificAlgebraicNestedSecondUniform.refines model root a p i hm hirr hv x hx ha hp htu hmir)
  · rw [prepare,ite_eq_right (fun h => hmir (hc.mp h)),reference,dite_eq_right hmir]
    exact PlayerSpecificAlgebraicDescriptorPad.refines _ 9 0 x _ hf

end Blotto.PlayerSpecificAlgebraicNestedSecondProfile
