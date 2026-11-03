import Blotto.PlayerSpecificPositiveFieldLowerBound

/-! Every actual initial sampler length has a computed positive dyadic
lower bound whose exponent is polynomial in the original input. This is
the quantitative termination certificate for the later halving search. -/
namespace Blotto.PlayerSpecificInitialPositivePrecision
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificPolynomialNormalization
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations PlayerSpecificAlgebraicInitialVector
set_option autoImplicit false
set_option maxHeartbeats 2500000

def inputSize {N : ℕ} (i : RationalPlayerSpecificInput N) : ℕ := PlayerSpecificRecognitionInputHeights.inputHeight i
def initialCoefficient : ℕ := (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3*
  (11*PlayerSpecificFiniteScaleHeights.coefficient+4)
def coefficient : ℕ := PlayerSpecificPositiveFieldLowerBound.coefficient*(initialCoefficient+1)

theorem base_le_height (H : ℕ) : H≤PlayerSpecificAlgebraicInitialHeights.height H := by
  have h1:=PlayerSpecificAlgebraicHeightEnvelope.large H
  have h2:=PlayerSpecificAlgebraicHeightEnvelope.large (PlayerSpecificAlgebraicHeightEnvelope.step H)
  have h3:=PlayerSpecificAlgebraicHeightEnvelope.large (PlayerSpecificAlgebraicHeightEnvelope.step (PlayerSpecificAlgebraicHeightEnvelope.step H))
  simp only [PlayerSpecificAlgebraicInitialHeights.height,PlayerSpecificAlgebraicHeightEnvelope.iterate]
  omega

theorem exponent_profile (C K N L H s : ℕ) (hH : H≤K*(N+1)*(L+1)) (hs : s≤C*(H+1)) :
    s≤(C*(K+1))*(N+1)*(L+1) := by
  have hpos : 1≤(N+1)*(L+1) := Nat.mul_le_mul (by omega : 1≤N+1) (by omega : 1≤L+1)
  have hh : H+1≤(K+1)*((N+1)*(L+1)) := by nlinarith only [hH,hpos]
  have hm:=Nat.mul_le_mul_left C hh
  nlinarith only [hs,hm]

theorem exponent_bound {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) (j : Fin N) :
    PlayerSpecificPositiveFieldLowerBound.exponent r.root.polynomial
      ((prepare RationalCostModel.schoolbook i r).rows.read j).length r.root.interval≤
        coefficient*(N+1)*(inputSize i+1) := by
  have hs:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hsize:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sizes i r hr
  have hm0 : r.root.polynomial≠[] := by intro hz; exact hs.2.1.ne_zero (by rw [hz]; rfl)
  have hred:=(reduced_rows RationalCostModel.schoolbook i r hs.1 hm0).2 j
  have hinit:=(PlayerSpecificAlgebraicInitialInputSizes.actual_sizes i r hr).2 j
  let H:=PlayerSpecificAlgebraicInitialInputSizes.height N (inputSize i)
  have hF : PlayerSpecificFiniteParameterSizes.height N (inputSize i)≤H := by
    exact (show PlayerSpecificFiniteParameterSizes.height N (inputSize i)≤PlayerSpecificAlgebraicInitialInputSizes.base N (inputSize i) by
      unfold PlayerSpecificAlgebraicInitialInputSizes.base; omega).trans (base_le_height _)
  have he : HasHeight [r.root.interval.lo,r.root.interval.hi] H :=
    cons_height (hsize.2.1.mono hF) (cons_height (hsize.2.2.1.mono hF) (nil_height _))
  have hal : ((prepare RationalCostModel.schoolbook i r).rows.read j).length.length≤3 := by
    have hl:=hred.1.2
    have hmLen:=hs.2.2.1
    omega
  have hp:=PlayerSpecificPositiveFieldLowerBound.polynomial_precision r.root.polynomial
    ((prepare RationalCostModel.schoolbook i r).rows.read j).length r.root.interval H
    (PlayerSpecificPolynomialHeights.mono hsize.1 hF) hinit.1 he hs.2.2.1 hal
  exact exponent_profile PlayerSpecificPositiveFieldLowerBound.coefficient initialCoefficient N (inputSize i) H _
    (PlayerSpecificAlgebraicInitialInputSizes.polynomial_height N (inputSize i)) hp

theorem actual_lower_bounds {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
      ∀ j,((PlayerSpecificPositiveFieldLowerBound.dyadic (PlayerSpecificPositiveFieldLowerBound.exponent r.root.polynomial
        ((prepare RationalCostModel.schoolbook i r).rows.read j).length r.root.interval)):ℝ)≤
          realEvaluate ((prepare RationalCostModel.schoolbook i r).rows.read j).length x ∧
        PlayerSpecificPositiveFieldLowerBound.exponent r.root.polynomial
          ((prepare RationalCostModel.schoolbook i r).rows.read j).length r.root.interval≤coefficient*(N+1)*(inputSize i+1) := by
  have hs:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  obtain ⟨x,hx,_,hred,hbox,_,_⟩:=PlayerSpecificAlgebraicInitialContract.actual_coupling_input i r hr
  refine ⟨x,hx,?_⟩
  intro j
  exact ⟨PlayerSpecificPositiveFieldLowerBound.positive_lower_bound r.root.polynomial _ r.root.interval hs.1 hs.2.1
    (hred j).1 x hx (hbox j).1.1,exponent_bound i r hr j⟩

end Blotto.PlayerSpecificInitialPositivePrecision
