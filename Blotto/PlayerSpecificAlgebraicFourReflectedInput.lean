import Blotto.PlayerSpecificAlgebraicFourMergedDraw

/-! Actual three-resource data for the reflected four-variable branch.
The existing resource engine receives computed capacities and initial rows
while retaining the original accepted parameter record and selected root. -/
namespace Blotto.PlayerSpecificAlgebraicFourReflectedInput
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Prepared where
  resources : PlayerSpecificAlgebraicInitialVector.Result 3
  long : FixedArrayTable 3 Data
  short : FixedArrayTable 3 Data
  budget : Data

def original (a : Input) : FixedArrayTable 3 Data := FixedArrayTable.ofFn ![a.first,a.second,a.third]

def prepare (model : RationalCostModel) (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) : Prepared :=
  let p := parameters model r.root a
  let long := original a
  let short := FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicField.times r.root.polynomial (p.read 4) (long.read j))
  let rows := FixedArrayTable.ofFn (fun j =>
    let capacity := PlayerSpecificAlgebraicField.times r.root.polynomial (p.read 5) (long.read j)
    let initial := PlayerSpecificAlgebraicField.times r.root.polynomial (p.read 6) capacity
    (⟨capacity,initial,initial⟩ : PlayerSpecificAlgebraicInitial.Result))
  ⟨⟨r,[],rows⟩,long,short,p.read 7⟩

theorem original_value (a : Input) (i : FourInput) (x : ℝ) (ha : PlayerSpecificAlgebraicFourInput.Values a i x) :
    ∀ j,realEvaluate ((original a).read j) x=i.originalLengths j := by
  intro j
  fin_cases j <;> simp only [original,FixedArrayTable.read_ofFn,FourInput.originalLengths]
  · exact ha.first
  · exact ha.second
  · exact ha.third

theorem values (model : RationalCostModel) (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (i : FourInput)
    (hm : Normalized r.root.polynomial) (hirr : Irreducible (semantics r.root.polynomial))
    (hv : r.root.interval.lo < r.root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits r.root a T)
    (hcase : i.w < (1-i.p)*i.ell) :
    (∀ j,realEvaluate ((prepare model r a).long.read j) x=(i.reflectedResourceSystem hcase).long j) ∧
      (∀ j,realEvaluate ((prepare model r a).short.read j) x=(i.reflectedResourceSystem hcase).short j) ∧
      (∀ j,realEvaluate (((prepare model r a).resources.rows.read j).length) x=(i.reflectedResourceSystem hcase).capacity j) ∧
      (∀ j,realEvaluate (((prepare model r a).resources.rows.read j).initialA) x=(i.reflectedResourceSystem hcase).initial j) ∧
      realEvaluate (prepare model r a).budget x=(i.reflectedResourceSystem hcase).M := by
  have hp := parameter_value model r.root a i hm hirr hv x hx ha T hfit
  have h4 : realEvaluate ((parameters model r.root a).read 4) x=i.shortFraction := hp 4
  have h5 : realEvaluate ((parameters model r.root a).read 5) x=i.scaleFraction := hp 5
  have h6 : realEvaluate ((parameters model r.root a).read 6) x=i.nestedProbability := hp 6
  have hl := original_value a i x ha
  refine ⟨hl,?_,?_,?_,hp 7⟩
  · intro j
    simp only [prepare,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicField.times_value _ _ _ x hx.1,h4,hl j]
    rfl
  · intro j
    simp only [prepare,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicField.times_value _ _ _ x hx.1,h5,hl j]
    exact (i.short_capacity j).symm
  · intro j
    simp only [prepare,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicField.times_value _ _ _ x hx.1,h6,h5,hl j]
    change i.nestedProbability*(i.scaleFraction*i.originalLengths j)=i.nestedProbability*i.scaleFraction*i.originalLengths j
    ring

end Blotto.PlayerSpecificAlgebraicFourReflectedInput
