import Blotto.PlayerSpecificAlgebraicDescriptorSwap

/-! Native endpoint and sorted-interior inputs for a closed mixture
weight. All six original rows retain their selected-root interpretation. -/
namespace Blotto.PlayerSpecificAlgebraicNestedSpecInput
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicDescriptorReference
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Values (a : Input) (i : NestedSpec) (x : ℝ) : Prop where
  budget : realEvaluate a.budget x=i.M
  first : realEvaluate a.first x=i.a
  second : realEvaluate a.second x=i.d
  long : realEvaluate a.long x=i.c
  short : realEvaluate a.short x=i.t
  probability : realEvaluate a.probability x=i.q

def endpoint (root : Candidate) (a : Input) (useShort : Bool) : PlayerSpecificAlgebraicThreeInput.Input :=
  ⟨a.budget,a.first,a.second,if useShort then a.short else a.long,PlayerSpecificAlgebraicField.constant root.polynomial 1⟩

def sorted (a : Input) (ordered : Bool) : Input :=
  if ordered then a else ⟨a.budget,a.second,a.first,a.long,a.short,a.probability⟩

theorem long_value (root : Candidate) (a : Input) (i : NestedSpec) (x : ℝ)
    (hx : realEvaluate root.polynomial x=0) (ha : Values a i x) (hq : i.q=0) :
    PlayerSpecificAlgebraicUnorderedThree.Values (endpoint root a false) (i.longInput hq) x := by
  refine ⟨ha.budget,ha.first,ha.second,ha.long,?_⟩
  simp only [endpoint,PlayerSpecificAlgebraicField.constant_value _ _ x hx,Rat.cast_one,NestedSpec.longInput]

theorem short_value (root : Candidate) (a : Input) (i : NestedSpec) (x : ℝ)
    (hx : realEvaluate root.polynomial x=0) (ha : Values a i x) (hq : i.q=1) :
    PlayerSpecificAlgebraicUnorderedThree.Values (endpoint root a true) (i.shortInput hq) x := by
  refine ⟨ha.budget,ha.first,ha.second,ha.short,?_⟩
  simp only [endpoint,PlayerSpecificAlgebraicField.constant_value _ _ x hx,Rat.cast_one,NestedSpec.shortInput]

theorem sorted_value (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedSpec)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : Values a i x) (hq0 : 0 < i.q) (hq1 : i.q < 1) :
    PlayerSpecificAlgebraicNestedInput.Values (sorted a (PlayerSpecificAlgebraicPairStep.le model root a.first a.second))
      (i.interiorInput hq0 hq1) x := by
  have hc := PlayerSpecificAlgebraicPairStep.le_correct model root a.first a.second hm hirr hv x hx
  rw [ha.first,ha.second] at hc
  by_cases had : i.a ≤ i.d
  · rw [sorted,ite_eq_left (hc.mpr had)]
    refine ⟨ha.budget,?_,?_,ha.long,ha.short,ha.probability⟩
    · simpa only [NestedSpec.interiorInput,min_eq_left had] using ha.first
    · simpa only [NestedSpec.interiorInput,max_eq_right had] using ha.second
  · rw [sorted,ite_eq_right (fun h => had (hc.mp h))]
    have hda := (lt_of_not_ge had).le
    refine ⟨ha.budget,?_,?_,ha.long,ha.short,ha.probability⟩
    · simpa only [NestedSpec.interiorInput,min_eq_right hda] using ha.second
    · simpa only [NestedSpec.interiorInput,max_eq_left hda] using ha.first

theorem three_refines (model : RationalCostModel) (root : Candidate) (a : PlayerSpecificAlgebraicThreeInput.Input) (i : ThreeSpec)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicUnorderedThree.Values a i x) :
    Refines (PlayerSpecificAlgebraicUnorderedThree.prepare model root a) x i.segmentLottery := by
  have h := PlayerSpecificAlgebraicUnorderedThree.fields model root a i hm hirr hv x hx ha
  refine ⟨h.1,?_,?_⟩
  · intro slot; funext j; exact h.2.1 slot j
  · intro slot; funext j; exact h.2.2 slot j

end Blotto.PlayerSpecificAlgebraicNestedSpecInput
