import Blotto.PlayerSpecificAlgebraicInitialCost

/-! Proof-only original-input views of the initial field calls with the
actual shared inverse value. The executing vector calls the field routine
directly with its cached inverse; it must never call these views. Its
one-time inverse execution and vector/list materialization are separate
enclosing callers. -/
namespace Blotto.PlayerSpecificAlgebraicInitialOriginalCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations PlayerSpecificAlgebraicInitialVector
set_option autoImplicit false
set_option maxHeartbeats 2500000

def inputSize {N : ℕ} (i : RationalPlayerSpecificInput N) : ℕ := PlayerSpecificRecognitionInputHeights.inputHeight i
def size (N L : ℕ) : ℕ := (N+1)*(L+1)
def heightCoefficient : ℕ := PlayerSpecificInitialPositivePrecision.initialCoefficient+1
def workCoefficient : ℕ := PlayerSpecificAlgebraicInitialCost.workCoefficient*heightCoefficient
def widthCoefficient : ℕ := PlayerSpecificAlgebraicInitialPrimitiveCost.widthCoefficient*heightCoefficient
def polynomialCoefficient : ℕ := workCoefficient*(widthCoefficient*widthCoefficient+widthCoefficient)

def fieldCall {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) (j : Fin N) :
    PlayerSpecificAlgebraicInitial.Result×ℕ :=
  PlayerSpecificAlgebraicInitialExecution.run RationalCostModel.schoolbook r.root
    (prepare RationalCostModel.schoolbook i r).inverseScale (i.valuesA.weight j) (i.valuesB.weight j)

theorem value {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) (j : Fin N) :
    (fieldCall i r j).1=(prepare RationalCostModel.schoolbook i r).rows.read j := by
  rw [fieldCall,PlayerSpecificAlgebraicInitialExecution.value,read]
  rfl

theorem height_profile (K N L H : ℕ) (hH : H≤K*(N+1)*(L+1)) : H+1≤(K+1)*((N+1)*(L+1)) := by
  have hp : 1≤(N+1)*(L+1) := Nat.mul_le_mul (by omega : 1≤N+1) (by omega : 1≤L+1)
  nlinarith only [hH,hp]

theorem height_polynomial (N L : ℕ) :
    PlayerSpecificAlgebraicInitialInputSizes.height N L+1≤heightCoefficient*size N L :=
  height_profile PlayerSpecificInitialPositivePrecision.initialCoefficient N L _
    (PlayerSpecificAlgebraicInitialInputSizes.polynomial_height N L)

theorem fixed_depth {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) (j : Fin N) :
    (fieldCall i r j).2≤PlayerSpecificAlgebraicInitialCost.workCoefficient*
      (PlayerSpecificAlgebraicInitialInputSizes.height N (inputSize i)+1)*
        RationalCostModel.schoolbook.rat (PlayerSpecificAlgebraicInitialPrimitiveCost.width
          (PlayerSpecificAlgebraicInitialInputSizes.height N (inputSize i))) := by
  have hs:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hp:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sizes i r hr
  have hm0 : r.root.polynomial≠[] := by intro hz; exact hs.2.1.ne_zero (by rw [hz]; rfl)
  let H:=PlayerSpecificAlgebraicInitialInputSizes.base N (inputSize i)
  have hF : PlayerSpecificFiniteParameterSizes.height N (inputSize i)≤H := by dsimp only [H,PlayerSpecificAlgebraicInitialInputSizes.base]; omega
  have hL : inputSize i≤H := by dsimp only [H,PlayerSpecificAlgebraicInitialInputSizes.base]; omega
  have hpos : 1≤H := by dsimp only [H,PlayerSpecificAlgebraicInitialInputSizes.base]; omega
  have hmH:=mono hp.1 hF
  have he:=cons_height (hp.2.1.mono hF) (cons_height (hp.2.2.1.mono hF) (nil_height _))
  have hweights:=PlayerSpecificRecognitionInputHeights.original_fields i
  have hi:=(reduced_rows RationalCostModel.schoolbook i r hs.1 hm0).1
  have hiH:=(PlayerSpecificAlgebraicInitialInputSizes.actual_sizes i r hr).1
  obtain ⟨x,hx,_⟩:=PlayerSpecificInitialPositivePrecision.actual_lower_bounds i r hr
  have hv : r.root.interval.lo<r.root.interval.hi := by exact_mod_cast hx.2.1.1.trans_le hx.2.1.2
  exact PlayerSpecificAlgebraicInitialCost.fixed_depth_source_cost RationalCostModel.schoolbook r.root _ _ _ H
    hs.1 hm0 hs.2.2.1 hmH he ((hweights.2.1 j).mono hL) ((hweights.2.2 j).mono hL) hpos hv hi hiH

theorem source_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) (j : Fin N) :
    (fieldCall i r j).2≤workCoefficient*size N (inputSize i)*
      RationalCostModel.schoolbook.rat (widthCoefficient*size N (inputSize i)) := by
  have hc:=fixed_depth i r hr j
  have hH:=height_polynomial N (inputSize i)
  have hm:=Nat.mul_le_mul_left PlayerSpecificAlgebraicInitialCost.workCoefficient hH
  have hw:=Nat.mul_le_mul_left PlayerSpecificAlgebraicInitialPrimitiveCost.widthCoefficient hH
  have hw' : PlayerSpecificAlgebraicInitialPrimitiveCost.width (PlayerSpecificAlgebraicInitialInputSizes.height N (inputSize i))≤
      widthCoefficient*size N (inputSize i) := by
    simpa only [PlayerSpecificAlgebraicInitialPrimitiveCost.width,widthCoefficient,Nat.mul_assoc] using hw
  have hbound:=hc.trans (Nat.mul_le_mul hm (RationalCostModel.schoolbook.monotone hw'))
  simpa only [workCoefficient,Nat.mul_assoc] using hbound

theorem polynomial_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) (j : Fin N) :
    (fieldCall i r j).2≤polynomialCoefficient*size N (inputSize i)^3 := by
  have hc:=source_cost i r hr j
  have hs : 1≤size N (inputSize i) := Nat.mul_le_mul (by omega : 1≤N+1) (by omega : 1≤ inputSize i+1)
  exact hc.trans (PlayerSpecificRootContract.schoolbook_profile workCoefficient widthCoefficient _ hs)

theorem all_field_calls {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    (∑ j,(fieldCall i r j).2)≤N*polynomialCoefficient*size N (inputSize i)^3 := by
  have h:=Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => polynomial_cost i r hr j)
  simpa [Nat.mul_assoc] using h

end Blotto.PlayerSpecificAlgebraicInitialOriginalCost
