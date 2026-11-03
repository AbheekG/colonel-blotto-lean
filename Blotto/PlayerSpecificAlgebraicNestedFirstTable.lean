import Blotto.PlayerSpecificAlgebraicDescriptorReference

/-! Actual first nested conditional table, including its zero corner.
The cached scalar probability controls a selected-only geometry branch. -/
namespace Blotto.PlayerSpecificAlgebraicNestedFirstTable
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicDescriptorReference
open PlayerSpecificAlgebraicCandidates (Candidate)
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def positive (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) : Bool :=
  !PlayerSpecificAlgebraicPairStep.le model root (scalar model root a extra 1) []

def zero (root : Candidate) (a : Input) (extra : Data) : Descriptor 3 9 :=
  ⟨FixedArrayTable.ofFn (fun slot => PlayerSpecificAlgebraicField.constant root.polynomial (if slot=0 then 1 else 0)),
    FixedArrayTable.ofFn (fun _ => FixedArrayTable.ofFn ![[],a.second,extra]),
    FixedArrayTable.ofFn (fun _ => FixedArrayTable.ofFn ![a.first,[],extra])⟩

def prepare (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) : Descriptor 3 9 :=
  if positive model root a extra then PlayerSpecificAlgebraicDescriptorShift.shift root extra
    (PlayerSpecificAlgebraicThreeGeometry.prepare model root (firstEnvironment model root a extra))
  else zero root a extra

noncomputable def reference (i : NestedInput) (htv : i.t≤ i.v) (s : ℝ) (hs : 0≤s ∧ s≤ i.t) : SegmentLottery 3 9 := by
  classical
  exact if hp : 0 < i.conditionalProbability s then
    let g:=i.firstGeometry htv s hs hp
    ⟨g.segmentLottery.weight,fun slot => shiftThird s (g.segmentLottery.P slot),
      fun slot => shiftThird s (g.segmentLottery.Q slot),g.segmentLottery.nonnegative,g.segmentLottery.mass⟩
  else ⟨fun slot => if slot=0 then 1 else 0,fun _ => ![0,i.d,s],fun _ => ![i.a,0,s],
    by intro slot; split <;> norm_num,by simp⟩

theorem positive_correct (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (extra : Data)
    (hEnv : ∀ j,Reduced root.polynomial ((environment a extra).read j)) :
    positive model root a extra=true ↔ 0 < i.conditionalProbability (realEvaluate extra x) := by
  have he:=scalar_value model root a i hm hirr hv x hx ha extra hEnv 1
  have hp : realEvaluate (scalar model root a extra 1) x=i.conditionalProbability (realEvaluate extra x) := by
    simpa [RealNestedParametersCode.scalarValues] using he
  have hz : realEvaluate [] x=0 := rfl
  simp only [positive,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,
    PlayerSpecificAlgebraicPairStep.le_correct model root _ _ hm hirr hv x hx,not_le,hp,hz]

theorem refines (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (extra : Data)
    (hEnv : ∀ j,Reduced root.polynomial ((environment a extra).read j))
    (htv : i.t≤ i.v) (hs : 0≤realEvaluate extra x ∧ realEvaluate extra x≤ i.t) :
    Refines (prepare model root a extra) x (reference i htv (realEvaluate extra x) hs) := by
  have hm0 : root.polynomial≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hc:=positive_correct model root a i hm hirr hv x hx ha extra hEnv
  by_cases hp : 0 < i.conditionalProbability (realEvaluate extra x)
  · rw [prepare,ite_eq_left (hc.mpr hp),reference,dite_eq_left hp]
    have hred : ∀ j,Reduced root.polynomial ((firstEnvironment model root a extra).read j) := by
      intro j
      rw [firstEnvironment,FixedArrayTable.read_ofFn]
      exact PlayerSpecificAlgebraicExpression.reduced model root _ _ hm hm0 hEnv
    have hf:=PlayerSpecificAlgebraicThreeGeometry.fields model root (firstEnvironment model root a extra) hm hirr hv x hx
      hred (i.firstGeometry htv (realEvaluate extra x) hs hp)
      (first_environment_value model root a i hm hirr hv x hx ha extra hEnv htv hs hp)
    have hshift:=PlayerSpecificAlgebraicDescriptorShift.fields root extra
      (PlayerSpecificAlgebraicThreeGeometry.prepare model root (firstEnvironment model root a extra)) x hx.1
    constructor
    · exact hf.1
    · intro slot
      rw [hshift.2.1 slot]
      congr 1
      funext j
      simpa only [values,ThreeGeometry.segmentLottery,RationalThreeGeometry.edges_real] using hf.2.1 slot j
    · intro slot
      rw [hshift.2.2 slot]
      congr 1
      funext j
      simpa only [values,ThreeGeometry.segmentLottery,RationalThreeGeometry.edges_real] using hf.2.2 slot j
  · rw [prepare,ite_eq_right (fun h => hp (hc.mp h)),reference,dite_eq_right hp]
    constructor
    · intro slot
      by_cases hslot : slot=0 <;> simp [zero,FixedArrayTable.read_ofFn,hslot,PlayerSpecificAlgebraicField.constant_value _ _ x hx.1]
    · intro slot
      funext j
      have hz : realEvaluate [] x=0 := rfl
      fin_cases j <;> simp [zero,values,FixedArrayTable.read_ofFn,hz,ha.second]
    · intro slot
      funext j
      have hz : realEvaluate [] x=0 := rfl
      fin_cases j <;> simp [zero,values,FixedArrayTable.read_ofFn,hz,ha.first]

end Blotto.PlayerSpecificAlgebraicNestedFirstTable
