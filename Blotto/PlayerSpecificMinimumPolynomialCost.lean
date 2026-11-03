import Blotto.PlayerSpecificMinimumGuardExecution

/-! An explicit original-input polynomial bounds guard measurement and
the actual halving loop together. Construction of the initial algebraic
vector and materialization of its cached length list are separate callers. -/
namespace Blotto.PlayerSpecificMinimumPolynomialCost
open PlayerSpecificMinimumOriginalSizes PlayerSpecificMinimumContract
set_option autoImplicit false
set_option maxHeartbeats 2500000

def workCoefficient : ℕ := (PlayerSpecificInitialPositivePrecision.coefficient+1)*
  PlayerSpecificMinimumSearchCost.coefficient*PlayerSpecificMinimumOriginalSizes.coefficient+8256
def widthCoefficient : ℕ := PlayerSpecificMinimumTestCost.widthCoefficient*PlayerSpecificMinimumOriginalSizes.coefficient+
  128*(PlayerSpecificInitialPositivePrecision.coefficient+1)+256
def polynomialCoefficient : ℕ := workCoefficient*(widthCoefficient*widthCoefficient+widthCoefficient)
def size (N L : ℕ) : ℕ := (N+1)*(L+1)

theorem size_positive (N L : ℕ) : 1≤size N L := Nat.mul_le_mul (by omega : 1≤N+1) (by omega : 1≤L+1)

theorem work_profile (P C K N S F H : ℕ) (hf : F=P*S) (hh : H+1≤K*S) (hS : 1≤S) :
    (F+1)*C*(N+1)*(H+1)≤((P+1)*C*K)*(N+1)*S^2 := by
  have hF : F+1≤(P+1)*S := by nlinarith only [hf,hS]
  have hm:=Nat.mul_le_mul hF hh
  have hc:=Nat.mul_le_mul_right (C*(N+1)) hm
  ring_nf at hc ⊢
  exact hc

theorem source_bound {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    (PlayerSpecificMinimumGuardExecution.run RationalCostModel.schoolbook i).2+(PlayerSpecificMinimumContract.run i r).work≤
      workCoefficient*(N+1)*size N (inputSize i)^2*
        RationalCostModel.schoolbook.rat (widthCoefficient*size N (inputSize i)) := by
  let S:=size N (inputSize i)
  let W:=widthCoefficient*S
  have hS : 1≤S := size_positive N (inputSize i)
  have hN : N+1≤S := by dsimp only [S,size]; nlinarith only [Nat.zero_le (N*inputSize i)]
  have hL : inputSize i+1≤S := by dsimp only [S,size]; nlinarith only [Nat.zero_le (N*inputSize i)]
  have hheight : height i+1≤PlayerSpecificMinimumOriginalSizes.coefficient*S := by
    simpa only [S,size,Nat.mul_assoc] using height_polynomial i
  have hfuel : fuel i=PlayerSpecificInitialPositivePrecision.coefficient*S := by
    simpa only [S,size,inputSize,Nat.mul_assoc] using fuel_value i
  have hwork:=work_profile PlayerSpecificInitialPositivePrecision.coefficient PlayerSpecificMinimumSearchCost.coefficient
    PlayerSpecificMinimumOriginalSizes.coefficient N S (fuel i) (height i) hfuel hheight hS
  have hwidth : PlayerSpecificMinimumTestCost.width (height i)≤W := by
    have hm:=Nat.mul_le_mul_left PlayerSpecificMinimumTestCost.widthCoefficient hheight
    have hc:=Nat.mul_le_mul_right S (show PlayerSpecificMinimumTestCost.widthCoefficient*
      PlayerSpecificMinimumOriginalSizes.coefficient≤widthCoefficient by unfold widthCoefficient; omega)
    unfold PlayerSpecificMinimumTestCost.width
    dsimp only [W,S,size] at *
    nlinarith only [hm,hc]
  have hs:=search_source_cost i r hr
  have hs':=hs.trans (Nat.mul_le_mul hwork (RationalCostModel.schoolbook.monotone hwidth))
  have hmwidth : PlayerSpecificInputWidthExecution.width (inputSize i)≤W := by
    have hh : 256*S≤W := by
      exact Nat.mul_le_mul_right S (show 256≤widthCoefficient by unfold widthCoefficient; omega)
    unfold PlayerSpecificInputWidthExecution.width
    nlinarith only [hL,hh]
  have hgwidth : PlayerSpecificMinimumGuardExecution.width PlayerSpecificInitialPositivePrecision.coefficient N (inputSize i)≤W := by
    have hc:=Nat.mul_le_mul_right S (show 128*(PlayerSpecificInitialPositivePrecision.coefficient+1)+256≤widthCoefficient by
      unfold widthCoefficient; omega)
    unfold PlayerSpecificMinimumGuardExecution.width
    dsimp only [W,S,size] at *
    nlinarith only [hc,hS]
  have hg:=PlayerSpecificMinimumGuardExecution.source_cost RationalCostModel.schoolbook i
  have hmmono:=RationalCostModel.schoolbook.monotone hmwidth
  have hgmono:=RationalCostModel.schoolbook.monotone hgwidth
  have hg' : (PlayerSpecificMinimumGuardExecution.run RationalCostModel.schoolbook i).2≤
      8256*S*RationalCostModel.schoolbook.rat W := by
    have hm:=Nat.mul_le_mul_left (4096*(2*N+2)*(inputSize i+1)) hmmono
    have hn:=Nat.mul_le_mul_left 64 hgmono
    have hu:=Nat.mul_le_mul_right (RationalCostModel.schoolbook.rat W) hS
    dsimp only [S,size,inputSize,PlayerSpecificInitialPositivePrecision.inputSize] at hg hm hn hu ⊢
    nlinarith only [hg,hm,hn,hu]
  have hT : S≤(N+1)*S^2 := by
    have hp:=Nat.mul_le_mul hN hS
    nlinarith only [hp,hS,Nat.zero_le (N*S*S)]
  have hscaled : 8256*S*RationalCostModel.schoolbook.rat W≤8256*((N+1)*S^2)*RationalCostModel.schoolbook.rat W := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 8256 (Nat.mul_le_mul_right (RationalCostModel.schoolbook.rat W) hT)
  have hgp:=hg'.trans hscaled
  unfold workCoefficient
  dsimp only [W,S] at hs' hgp
  nlinarith only [hs',hgp]

theorem polynomial_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    (PlayerSpecificMinimumGuardExecution.run RationalCostModel.schoolbook i).2+(PlayerSpecificMinimumContract.run i r).work≤
      polynomialCoefficient*(N+1)*size N (inputSize i)^4 := by
  have hs:=source_bound i r hr
  have hp:=PlayerSpecificFiniteParameterCost.schoolbook_profile workCoefficient widthCoefficient
    ((N+1)*size N (inputSize i)^2) (size N (inputSize i)) (size_positive N (inputSize i))
  have hc : workCoefficient*(N+1)*size N (inputSize i)^2*
      RationalCostModel.schoolbook.rat (widthCoefficient*size N (inputSize i))≤
      polynomialCoefficient*(N+1)*size N (inputSize i)^4 := by
    unfold polynomialCoefficient
    ring_nf at hp ⊢
    exact hp
  exact hs.trans hc

end Blotto.PlayerSpecificMinimumPolynomialCost
