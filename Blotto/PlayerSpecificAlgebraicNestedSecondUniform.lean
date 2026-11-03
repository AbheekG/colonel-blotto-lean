import Blotto.PlayerSpecificAlgebraicNestedCaseParameters

/-! Actual three-variable uniform component of the second nested case.
The reached mirror row supplies both the reduced budget and final shift. -/
namespace Blotto.PlayerSpecificAlgebraicNestedSecondUniform
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicDescriptorReference
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
open PlayerSpecificAlgebraicCandidates (Candidate)
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def input (root : Candidate) (a : Input) (p : Prepared) : PlayerSpecificAlgebraicThreeInput.Input :=
  ⟨PlayerSpecificAlgebraicField.minus root.polynomial a.budget p.mirror,a.first,a.second,
    PlayerSpecificAlgebraicField.minus root.polynomial a.short p.mirror,PlayerSpecificAlgebraicField.constant root.polynomial 1⟩

def prepare (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) : Descriptor 3 9 :=
  PlayerSpecificAlgebraicDescriptorShift.shift root p.mirror (PlayerSpecificAlgebraicOrderedThree.prepare model root (input root a p))

noncomputable def reference (i : NestedInput) (htu : i.u≤ i.t) (hmir : i.mirrorLength< i.t) : SegmentLottery 3 9 :=
  (i.secondUniformInput htu hmir).segmentLottery.mapped (AffineAllocation.shiftThird i.mirrorLength)

theorem input_value (root : Candidate) (a : Input) (p : Prepared) (i : NestedInput) (x : ℝ)
    (hx : realEvaluate root.polynomial x=0) (ha : PlayerSpecificAlgebraicNestedInput.Values a i x)
    (hp : PlayerSpecificAlgebraicNestedCaseParameters.Values p i x) (htu : i.u≤ i.t) (hmir : i.mirrorLength< i.t) :
    PlayerSpecificAlgebraicThreeInput.Values (input root a p) (i.secondUniformInput htu hmir) x := by
  constructor
  · simp only [input,PlayerSpecificAlgebraicField.minus_value _ _ _ x hx,ha.budget,hp.mirror,NestedInput.secondUniformInput]
  · exact ha.first
  · exact ha.second
  · simp only [input,PlayerSpecificAlgebraicField.minus_value _ _ _ x hx,ha.short,hp.mirror,NestedInput.secondUniformInput]
  · simp only [input,PlayerSpecificAlgebraicField.constant_value _ _ x hx,Rat.cast_one,NestedInput.secondUniformInput]

theorem refines (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (hp : PlayerSpecificAlgebraicNestedCaseParameters.Values p i x)
    (htu : i.u≤ i.t) (hmir : i.mirrorLength< i.t) :
    Refines (prepare model root a p) x (reference i htu hmir) := by
  have hf:=PlayerSpecificAlgebraicOrderedThree.fields model root (input root a p) (i.secondUniformInput htu hmir)
    hm hirr hv x hx (input_value root a p i x hx.1 ha hp htu hmir)
  constructor
  · exact hf.1
  · intro slot
    rw [prepare,PlayerSpecificAlgebraicDescriptorShift.shift,FixedArrayTable.read_ofFn,
      PlayerSpecificAlgebraicDescriptorShift.row_value root p.mirror _ x hx.1,hp.mirror]
    change shiftThird i.mirrorLength _=shiftThird i.mirrorLength _
    congr 1
    funext j
    exact hf.2.1 slot j
  · intro slot
    rw [prepare,PlayerSpecificAlgebraicDescriptorShift.shift,FixedArrayTable.read_ofFn,
      PlayerSpecificAlgebraicDescriptorShift.row_value root p.mirror _ x hx.1,hp.mirror]
    change shiftThird i.mirrorLength _=shiftThird i.mirrorLength _
    congr 1
    funext j
    exact hf.2.2 slot j

end Blotto.PlayerSpecificAlgebraicNestedSecondUniform
