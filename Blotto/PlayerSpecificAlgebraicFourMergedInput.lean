import Blotto.PlayerSpecificAlgebraicSplitFirstTwo

/-! Actual scaled-uniform input of the small four-variable branch. The
three scaled lengths and merged child are computed from one parameter table. -/
namespace Blotto.PlayerSpecificAlgebraicFourMergedInput
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Prepared where
  first : Data
  second : Data
  child : PlayerSpecificAlgebraicThreeInput.Input

def prepare (model : RationalCostModel) (root : Candidate) (a : Input) : Prepared :=
  let p := parameters model root a
  let scale := p.read 5
  let first := PlayerSpecificAlgebraicField.times root.polynomial scale a.first
  let second := PlayerSpecificAlgebraicField.times root.polynomial scale a.second
  let third := PlayerSpecificAlgebraicField.times root.polynomial scale a.third
  ⟨first,second,⟨a.budget,PlayerSpecificAlgebraicField.plus root.polynomial first second,third,a.length,
    PlayerSpecificAlgebraicField.constant root.polynomial 1⟩⟩

theorem values (model : RationalCostModel) (root : Candidate) (a : Input) (i : FourInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hcase : i.w < (1-i.p)*i.ell) :
    realEvaluate (prepare model root a).first x=(i.smallUniformInput hcase).l0 ∧
      realEvaluate (prepare model root a).second x=(i.smallUniformInput hcase).l1 ∧
      PlayerSpecificAlgebraicUnorderedThree.Values (prepare model root a).child (i.smallUniformInput hcase).childSpec x := by
  have hp := parameter_value model root a i hm hirr hv x hx ha T hfit 5
  have hs : realEvaluate ((parameters model root a).read 5) x=i.scaleFraction := hp
  have hfirst : realEvaluate (prepare model root a).first x=i.scaleFraction*i.u := by
    simp only [prepare,PlayerSpecificAlgebraicField.times_value _ _ _ x hx.1,hs,ha.first]
  have hsecond : realEvaluate (prepare model root a).second x=i.scaleFraction*i.v := by
    simp only [prepare,PlayerSpecificAlgebraicField.times_value _ _ _ x hx.1,hs,ha.second]
  refine ⟨hfirst,hsecond,?_⟩
  refine ⟨ha.budget,?_,?_,ha.length,?_⟩
  · simp only [prepare,PlayerSpecificAlgebraicField.plus_value _ _ _ x hx.1,
      PlayerSpecificAlgebraicField.times_value _ _ _ x hx.1,hs,ha.first,ha.second,
      FourInput.smallUniformInput,MergeFourInput.childSpec]
  · simp only [prepare,PlayerSpecificAlgebraicField.times_value _ _ _ x hx.1,hs,ha.third,
      FourInput.smallUniformInput,MergeFourInput.childSpec]
  · simp only [prepare,PlayerSpecificAlgebraicField.constant_value _ _ x hx.1,Rat.cast_one,
      FourInput.smallUniformInput,MergeFourInput.childSpec]

end Blotto.PlayerSpecificAlgebraicFourMergedInput
