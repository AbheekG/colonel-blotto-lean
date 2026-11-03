import Blotto.PlayerSpecificInitialMinimumValues

/-! Parent copies, measured address words and reference returns in the
initial/minimum preparation have polynomial original-input cost. -/
namespace Blotto.PlayerSpecificInitialMinimumParentCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicInitialVectorBudget PlayerSpecificInitialMinimumValues
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local irreducible] PlayerSpecificMinimumSearch.search

def minimumWidthCoefficient : ℕ := PlayerSpecificMinimumTestCost.widthCoefficient*PlayerSpecificMinimumOriginalSizes.coefficient
def polynomialCoefficient : ℕ := 100*(minimumWidthCoefficient*minimumWidthCoefficient+minimumWidthCoefficient)+
  2560*(widthCoefficient*widthCoefficient+widthCoefficient)

theorem minimum_width {N : ℕ} (i : RationalPlayerSpecificInput N) :
    PlayerSpecificMinimumTestCost.width (PlayerSpecificMinimumOriginalSizes.height i)≤minimumWidthCoefficient*size N (inputSize i) := by
  have h:=Nat.mul_le_mul_left PlayerSpecificMinimumTestCost.widthCoefficient (PlayerSpecificMinimumOriginalSizes.height_polynomial i)
  simpa only [PlayerSpecificMinimumTestCost.width,minimumWidthCoefficient,size,
    PlayerSpecificMinimumOriginalSizes.inputSize,PlayerSpecificInitialPositivePrecision.inputSize,inputSize,Nat.mul_assoc] using h

theorem frame_profile (model : RationalCostModel) (N s W : ℕ) (q : ℚ)
    (hq : price model (copyRow [q])≤66*model.rat W)
    (hN : price model [.control N]≤3*model.rat W)
    (hs : price model [.control s]≤3*model.rat W)
    (hone : price model [.control 1]≤3*model.rat W) :
    price model (PlayerSpecificInitialMinimumExecution.frame N q s)≤100*model.rat W := by
  simp only [PlayerSpecificInitialMinimumExecution.frame,price,List.map_append,List.sum_append,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at *
  omega

theorem frame_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    price RationalCostModel.schoolbook (PlayerSpecificInitialMinimumExecution.frame N (minimum i r).quantum (minimum i r).exponent)≤
      100*RationalCostModel.schoolbook.rat (PlayerSpecificMinimumTestCost.width (PlayerSpecificMinimumOriginalSizes.height i)) := by
  have hs:=PlayerSpecificMinimumOriginalSizes.output_size i r hr
  obtain ⟨_,_,_,_,he,_,_⟩:=PlayerSpecificMinimumContract.actual_contract i r hr
  have hN : N≤PlayerSpecificMinimumOriginalSizes.height i := by unfold PlayerSpecificMinimumOriginalSizes.height; omega
  have hsBound : (PlayerSpecificMinimumContract.run i r).exponent≤PlayerSpecificMinimumOriginalSizes.height i := by
    unfold PlayerSpecificMinimumOriginalSizes.height
    omega
  have hcopy:=PlayerSpecificMinimumTestCost.row_copy RationalCostModel.schoolbook [(PlayerSpecificMinimumContract.run i r).quantum]
    (PlayerSpecificMinimumOriginalSizes.height i) (cons_height hs.1 (nil_height _)) (by simp)
  have hn:=PlayerSpecificMinimumTestCost.control RationalCostModel.schoolbook N (PlayerSpecificMinimumOriginalSizes.height i) (by omega)
  have hexp:=PlayerSpecificMinimumTestCost.control RationalCostModel.schoolbook (PlayerSpecificMinimumContract.run i r).exponent
    (PlayerSpecificMinimumOriginalSizes.height i) (by omega)
  have hone:=PlayerSpecificMinimumTestCost.control RationalCostModel.schoolbook 1 (PlayerSpecificMinimumOriginalSizes.height i) (by omega)
  have hold:=frame_profile RationalCostModel.schoolbook N (PlayerSpecificMinimumContract.run i r).exponent
    (PlayerSpecificMinimumTestCost.width (PlayerSpecificMinimumOriginalSizes.height i)) (PlayerSpecificMinimumContract.run i r).quantum hcopy hn hexp hone
  have heq:=congrArg (fun result : PlayerSpecificMinimumSearch.Result =>
    price RationalCostModel.schoolbook (PlayerSpecificInitialMinimumExecution.frame N result.quantum result.exponent)) (minimum_value i r)
  exact heq.symm ▸ hold

 theorem source_profile (N A measured frame R T : ℕ) (hm : measured≤512*(N+1)*T)
    (hf : frame≤100*R) (ha : A≤64*T) :
    measured+frame+32*(N+1)*A≤100*R+2560*(N+1)*T := by
  have hp:=Nat.mul_le_mul_left (32*(N+1)) ha
  nlinarith only [hm,hf,hp]

theorem source_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    (PlayerSpecificWidthExecution.run RationalCostModel.schoolbook (N+1)).2+
      price RationalCostModel.schoolbook (PlayerSpecificInitialMinimumExecution.frame N (minimum i r).quantum (minimum i r).exponent)+32*(N+1)*address N≤
        100*RationalCostModel.schoolbook.rat (minimumWidthCoefficient*size N (inputSize i))+
          2560*(N+1)*RationalCostModel.schoolbook.rat (width N (inputSize i)) := by
  have hf:=frame_cost i r hr
  have hfw:=Nat.mul_le_mul_left 100 (RationalCostModel.schoolbook.monotone (minimum_width i))
  have hm:=PlayerSpecificAlgebraicInitialVectorStages.measurement_cost i
  have ha:=(address_bounds N (inputSize i)).2.1
  exact source_profile N (address N) _ _ _ _ hm (hf.trans hfw) ha

 theorem polynomial_profile (N S D E t : ℕ) (hS : 1≤S)
    (ht : t≤100*RationalCostModel.schoolbook.rat (D*S)+2560*(N+1)*RationalCostModel.schoolbook.rat (E*S)) :
    t≤(100*(D*D+D)+2560*(E*E+E))*(N+1)*S^2 := by
  have hmin:=PlayerSpecificFiniteParameterCost.schoolbook_profile 100 D 1 S hS
  have hmin' : 100*RationalCostModel.schoolbook.rat (D*S)≤(100*(D*D+D))*(N+1)*S^2 := by
    have hm:=Nat.mul_le_mul_right ((100*(D*D+D))*S^2) (show 1≤N+1 by omega)
    ring_nf at hmin hm ⊢
    exact hmin.trans hm
  have hv:=PlayerSpecificFiniteParameterCost.schoolbook_profile 2560 E (N+1) S hS
  nlinarith only [ht,hmin',hv]

theorem polynomial_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    (PlayerSpecificWidthExecution.run RationalCostModel.schoolbook (N+1)).2+
      price RationalCostModel.schoolbook (PlayerSpecificInitialMinimumExecution.frame N (minimum i r).quantum (minimum i r).exponent)+32*(N+1)*address N≤
        polynomialCoefficient*(N+1)*size N (inputSize i)^2 := by
  have hc:=source_cost i r hr
  dsimp only [width] at hc
  have h:=polynomial_profile N (size N (inputSize i)) minimumWidthCoefficient widthCoefficient _ (size_bounds N (inputSize i)).1 hc
  simpa only [polynomialCoefficient] using h

end Blotto.PlayerSpecificInitialMinimumParentCost
