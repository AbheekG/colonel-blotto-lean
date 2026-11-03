import Blotto.PlayerSpecificAlgebraicNestedSpecInputSizes

/-! Actual closed-weight nested descriptors: q=0/1 use the appropriate
three-variable core; the interior sorts once and restores coordinates. -/
namespace Blotto.PlayerSpecificAlgebraicNestedSpecProfile
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes
open PlayerSpecificAlgebraicNestedSpecInput PlayerSpecificAlgebraicDescriptorReference PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def qZero (model : RationalCostModel) (root : Candidate) (a : Input) : Bool :=
  PlayerSpecificAlgebraicPairStep.le model root a.probability []

def qOne (model : RationalCostModel) (root : Candidate) (a : Input) : Bool :=
  PlayerSpecificAlgebraicPairStep.le model root (PlayerSpecificAlgebraicField.constant root.polynomial 1) a.probability

def interior (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) : Descriptor 3 18 :=
  let ordered := PlayerSpecificAlgebraicPairStep.le model root a.first a.second
  let table := PlayerSpecificAlgebraicNestedInteriorProfile.prepare model root (sorted a ordered) K outer
  if ordered then table else PlayerSpecificAlgebraicDescriptorSwap.swap table

def prepare (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) : Descriptor 3 18 :=
  if qZero model root a then PlayerSpecificAlgebraicDescriptorPad.pad
    (PlayerSpecificAlgebraicUnorderedThree.prepare model root (endpoint root a false)) 9 0
  else if qOne model root a then PlayerSpecificAlgebraicDescriptorPad.pad
    (PlayerSpecificAlgebraicUnorderedThree.prepare model root (endpoint root a true)) 9 0
  else interior model root a K outer

noncomputable def interiorReference (i : NestedSpec) (hq0 : 0 < i.q) (hq1 : i.q < 1) (K : ℕ) (outer : Fin K → Bool) :
    SegmentLottery 3 18 := by
  classical
  let j := i.interiorInput hq0 hq1
  let table := PlayerSpecificAlgebraicNestedInteriorProfile.reference j K outer
  exact if i.a ≤ i.d then table else table.mapped AffineAllocation.swapFirst

noncomputable def reference (i : NestedSpec) (K : ℕ) (outer : Fin K → Bool) : SegmentLottery 3 18 := by
  classical
  exact if hq0 : i.q=0 then PlayerSpecificSegmentAssemblyReference.pad (i.longInput hq0).segmentLottery 9 0
  else if hq1 : i.q=1 then PlayerSpecificSegmentAssemblyReference.pad (i.shortInput hq1).segmentLottery 9 0
  else interiorReference i (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1) K outer

theorem zero_correct (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedSpec)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) (ha : PlayerSpecificAlgebraicNestedSpecInput.Values a i x) :
    qZero model root a=true ↔ i.q=0 := by
  have hz : realEvaluate [] x=0 := rfl
  rw [qZero,PlayerSpecificAlgebraicPairStep.le_correct model root _ _ hm hirr hv x hx,ha.probability,hz]
  exact ⟨fun h => le_antisymm h i.q_nonneg,fun h => h.le⟩

theorem one_correct (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedSpec)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) (ha : PlayerSpecificAlgebraicNestedSpecInput.Values a i x) :
    qOne model root a=true ↔ i.q=1 := by
  rw [qOne,PlayerSpecificAlgebraicPairStep.le_correct model root _ _ hm hirr hv x hx,
    PlayerSpecificAlgebraicField.constant_value _ _ x hx.1,Rat.cast_one,ha.probability]
  exact ⟨fun h => le_antisymm i.q_le h,fun h => h.symm.le⟩

theorem interior_refines (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedSpec)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) (ha : PlayerSpecificAlgebraicNestedSpecInput.Values a i x)
    (T : ℕ) (hfit : Fits root a T) (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T)
    (hq0 : 0 < i.q) (hq1 : i.q < 1) (K : ℕ) (outer : Fin K → Bool) :
    Refines (interior model root a K outer) x (interiorReference i hq0 hq1 K outer) := by
  let ordered := PlayerSpecificAlgebraicPairStep.le model root a.first a.second
  let raw := sorted a ordered
  let j := i.interiorInput hq0 hq1
  have hr := PlayerSpecificAlgebraicNestedInteriorProfile.refines model root raw j hm hirr hv x hx
    (sorted_value model root a i hm hirr hv x hx ha hq0 hq1) T
    (PlayerSpecificAlgebraicNestedSpecInputSizes.sorted_fits root a ordered T hfit) hml hmT hT K outer
  have hc := PlayerSpecificAlgebraicPairStep.le_correct model root a.first a.second hm hirr hv x hx
  rw [ha.first,ha.second] at hc
  by_cases had : i.a ≤ i.d
  · simpa only [interior,ite_eq_left (hc.mpr had),interiorReference,ite_eq_left had] using hr
  · rw [interior,ite_eq_right (fun h => had (hc.mp h)),interiorReference,ite_eq_right had]
    exact PlayerSpecificAlgebraicDescriptorSwap.refines _ x _ hr

theorem refines (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedSpec)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) (ha : PlayerSpecificAlgebraicNestedSpecInput.Values a i x)
    (T : ℕ) (hfit : Fits root a T) (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T)
    (K : ℕ) (outer : Fin K → Bool) : Refines (prepare model root a K outer) x (reference i K outer) := by
  have hz := zero_correct model root a i hm hirr hv x hx ha
  have ho := one_correct model root a i hm hirr hv x hx ha
  by_cases hq0 : i.q=0
  · rw [prepare,ite_eq_left (hz.mpr hq0),reference,dite_eq_left hq0]
    exact PlayerSpecificAlgebraicDescriptorPad.refines _ 9 0 x _
      (three_refines model root (endpoint root a false) (i.longInput hq0) hm hirr hv x hx (long_value root a i x hx.1 ha hq0))
  · rw [prepare,ite_eq_right (fun h => hq0 (hz.mp h)),reference,dite_eq_right hq0]
    by_cases hq1 : i.q=1
    · rw [ite_eq_left (ho.mpr hq1),dite_eq_left hq1]
      exact PlayerSpecificAlgebraicDescriptorPad.refines _ 9 0 x _
        (three_refines model root (endpoint root a true) (i.shortInput hq1) hm hirr hv x hx (short_value root a i x hx.1 ha hq1))
    · rw [ite_eq_right (fun h => hq1 (ho.mp h)),dite_eq_right hq1]
      exact interior_refines model root a i hm hirr hv x hx ha T hfit hml hmT hT
        (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1) K outer

end Blotto.PlayerSpecificAlgebraicNestedSpecProfile
