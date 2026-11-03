import Blotto.PlayerSpecificAlgebraicNestedFirstProfile

/-! All ordered interior nested cases share one actual algebraic
dispatcher. Its six case parameters are computed and retained once. -/
namespace Blotto.PlayerSpecificAlgebraicNestedInteriorProfile
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicDescriptorReference PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def selected (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (K : ℕ) (outer : Fin K → Bool) :
    Descriptor 3 18 :=
  if PlayerSpecificAlgebraicPairStep.le model root a.short p.v then
    PlayerSpecificAlgebraicNestedFirstProfile.prepare model root a K outer
  else if PlayerSpecificAlgebraicPairStep.le model root p.u a.short then
    PlayerSpecificAlgebraicNestedSecondProfile.prepare model root a p K outer
  else PlayerSpecificAlgebraicNestedThirdProfile.prepare model root a p K outer

def prepare (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) : Descriptor 3 18 :=
  let p := PlayerSpecificAlgebraicNestedCaseParameters.prepare model root a
  selected model root a p K outer

noncomputable def reference (i : NestedInput) (K : ℕ) (outer : Fin K → Bool) : SegmentLottery 3 18 := by
  classical
  exact if htv : i.t ≤ i.v then PlayerSpecificAlgebraicNestedFirstProfile.reference i htv K outer
  else if htu : i.u ≤ i.t then PlayerSpecificAlgebraicNestedSecondProfile.reference i htu K outer
  else PlayerSpecificAlgebraicNestedThirdProfile.reference i (lt_of_not_ge htv) (lt_of_not_ge htu) K outer

theorem selected_refines (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (hp : PlayerSpecificAlgebraicNestedCaseParameters.Values p i x)
    (T : ℕ) (hfit : Fits root a T) (hpb : PlayerSpecificAlgebraicNestedCaseParameters.Bounds root p T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T)
    (K : ℕ) (outer : Fin K → Bool) : Refines (selected model root a p K outer) x (reference i K outer) := by
  have hc1 : PlayerSpecificAlgebraicPairStep.le model root a.short p.v=true ↔ i.t ≤ i.v := by
    rw [PlayerSpecificAlgebraicPairStep.le_correct model root _ _ hm hirr hv x hx,ha.short,hp.v]
  have hc2 : PlayerSpecificAlgebraicPairStep.le model root p.u a.short=true ↔ i.u ≤ i.t := by
    rw [PlayerSpecificAlgebraicPairStep.le_correct model root _ _ hm hirr hv x hx,hp.u,ha.short]
  by_cases htv : i.t ≤ i.v
  · rw [selected,ite_eq_left (hc1.mpr htv),reference,dite_eq_left htv]
    exact PlayerSpecificAlgebraicNestedFirstProfile.refines model root a i hm hirr hv x hx ha T hfit htv K outer
  · rw [selected,ite_eq_right (fun h => htv (hc1.mp h)),reference,dite_eq_right htv]
    by_cases htu : i.u ≤ i.t
    · rw [ite_eq_left (hc2.mpr htu),dite_eq_left htu]
      exact PlayerSpecificAlgebraicNestedSecondProfile.refines model root a p i hm hirr hv x hx ha hp T hfit hpb hml hmT hT htu K outer
    · rw [ite_eq_right (fun h => htu (hc2.mp h)),dite_eq_right htu]
      exact PlayerSpecificAlgebraicNestedThirdProfile.refines model root a p i hm hirr hv x hx ha hp T hfit hpb hml hmT hT
        (lt_of_not_ge htv) (lt_of_not_ge htu) K outer

theorem refines (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T)
    (K : ℕ) (outer : Fin K → Bool) : Refines (prepare model root a K outer) x (reference i K outer) := by
  have hm0 : root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  let p := PlayerSpecificAlgebraicNestedCaseParameters.prepare model root a
  have hp := PlayerSpecificAlgebraicNestedCaseParameters.values model root a i hm hirr hv x hx ha T hfit
  have hb := PlayerSpecificAlgebraicNestedCaseParameters.bounds model root a T hfit hm hm0 hml hmT hT
  have hi := PlayerSpecificAlgebraicExpressionBudget.initial_le 9 T
  exact selected_refines model root a p i hm hirr hv x hx ha hp (iterate 9 T)
    (PlayerSpecificAlgebraicNestedInputTools.fits_mono root a T _ hfit hi) hb hml (mono hmT hi) (hT.trans hi) K outer

theorem budget (i : NestedInput) (K : ℕ) (outer : Fin K → Bool) :
    ∀ slot,FullBudget i.M ((reference i K outer).P slot) ∧ FullBudget i.M ((reference i K outer).Q slot) := by
  unfold reference
  split
  · exact PlayerSpecificAlgebraicNestedFirstProfile.budget i _ K outer
  · split
    · exact PlayerSpecificAlgebraicNestedRemainingProperties.second_budget i _ K outer
    · exact PlayerSpecificAlgebraicNestedRemainingProperties.third_budget i _ _ K outer

theorem box (i : NestedInput) (K : ℕ) (outer : Fin K → Bool) :
    ∀ slot,InBox ![i.a,i.d,i.c] ((reference i K outer).P slot) ∧ InBox ![i.a,i.d,i.c] ((reference i K outer).Q slot) := by
  unfold reference
  split
  · exact PlayerSpecificAlgebraicNestedFirstProfile.box i _ K outer
  · split
    · exact PlayerSpecificAlgebraicNestedRemainingProperties.second_box i _ K outer
    · exact PlayerSpecificAlgebraicNestedRemainingProperties.third_box i _ _ K outer

end Blotto.PlayerSpecificAlgebraicNestedInteriorProfile
