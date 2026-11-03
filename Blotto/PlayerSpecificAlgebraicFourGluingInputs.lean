import Blotto.PlayerSpecificAlgebraicFourInput

/-! The two actual three-variable gluing inputs reuse one cached
four-parameter table. Their exact laws are the paper's auxiliary laws. -/
namespace Blotto.PlayerSpecificAlgebraicFourGluingInputs
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicFourInput PlayerSpecificAlgebraicDescriptorReference
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def first (root : Candidate) (a : Input) (p : FixedArrayTable 8 Data) : PlayerSpecificAlgebraicThreeInput.Input :=
  ⟨p.read 2,a.first,a.second,p.read 1,PlayerSpecificAlgebraicField.constant root.polynomial 1⟩

def second (a : Input) (p : FixedArrayTable 8 Data) : PlayerSpecificAlgebraicThreeInput.Input :=
  ⟨p.read 3,p.read 1,a.third,a.length,a.probability⟩

theorem first_value (root : Candidate) (a : Input) (p : FixedArrayTable 8 Data) (i : FourInput) (x : ℝ)
    (hx : realEvaluate root.polynomial x=0) (ha : PlayerSpecificAlgebraicFourInput.Values a i x)
    (hp : ∀ j,realEvaluate (p.read j) x=RealFourParametersCode.values i j) (hcase : (1-i.p)*i.ell ≤ i.w) :
    PlayerSpecificAlgebraicUnorderedThree.Values (first root a p) (i.gluingFirstSpec hcase) x := by
  refine ⟨hp 2,ha.first,ha.second,hp 1,?_⟩
  simp only [first,PlayerSpecificAlgebraicField.constant_value _ _ x hx,Rat.cast_one,FourInput.gluingFirstSpec]

theorem second_value (a : Input) (p : FixedArrayTable 8 Data) (i : FourInput) (x : ℝ) (ha : PlayerSpecificAlgebraicFourInput.Values a i x)
    (hp : ∀ j,realEvaluate (p.read j) x=RealFourParametersCode.values i j) (hcase : (1-i.p)*i.ell ≤ i.w) :
    PlayerSpecificAlgebraicUnorderedThree.Values (second a p) (i.gluingSecondSpec hcase) x :=
  ⟨hp 3,hp 1,ha.third,ha.length,ha.probability⟩

end Blotto.PlayerSpecificAlgebraicFourGluingInputs
