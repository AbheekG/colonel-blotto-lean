import Blotto.PlayerSpecificAlgebraicInitialVectorStages

/-! Complete one-time algebraic initial-vector source cost, including
actual input arrays, one inverse, every cached field call, array indices,
returned descriptors, rational copies and enclosing controls. -/
namespace Blotto.PlayerSpecificAlgebraicInitialVectorCost
open PlayerSpecificAlgebraicInitialVectorBudget PlayerSpecificAlgebraicInitialVectorStages
set_option autoImplicit false
set_option maxHeartbeats 2500000

def polynomialCoefficient : ℕ := workCoefficient*(widthCoefficient*widthCoefficient+widthCoefficient)

theorem profile (C N S R A measured first second inverse rows frame : ℕ) (hS : 1≤S)
    (hA : A≤64*R) (hm : measured≤512*(N+1)*R) (hfirst : first≤10000*(N+1)*R)
    (hsecond : second≤10000*(N+1)*R) (hi : inverse≤7000000000*R)
    (hr : rows≤N*(C*S*R)+44*(N+1)*A) (hf : frame≤140*R) :
    measured+first+second+inverse+rows+frame+64*(N+1)*A≤(C+8000000000)*(N+1)*S*R := by
  have hNR : (N+1)*R≤(N+1)*S*R := by
    have h:=Nat.mul_le_mul_right ((N+1)*R) hS
    ring_nf at h ⊢
    exact h
  have hR : R≤(N+1)*S*R := by
    have hp : 1≤(N+1)*S := Nat.mul_le_mul (by omega : 1≤N+1) hS
    simpa only [one_mul] using Nat.mul_le_mul_right R hp
  have hrow : N*(C*S*R)≤C*(N+1)*S*R := by
    nlinarith only [Nat.zero_le (C*S*R)]
  have haddr:=Nat.mul_le_mul_left (108*(N+1)) hA
  nlinarith only [hm,hfirst,hsecond,hi,hr,hf,hNR,hR,hrow,haddr]

theorem price_eq {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) :
    (PlayerSpecificAlgebraicInitialVectorExecution.run RationalCostModel.schoolbook i r).2=
      (PlayerSpecificWidthExecution.run RationalCostModel.schoolbook (N+1)).2+(first i).2+(second i).2+
      (inverse r).2+(rows i r).2+PlayerSpecificRationalTrace.price RationalCostModel.schoolbook
        (PlayerSpecificAlgebraicInitialVectorExecution.frame i (inverse r).1)+64*(N+1)*address N := rfl

theorem source_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    (PlayerSpecificAlgebraicInitialVectorExecution.run RationalCostModel.schoolbook i r).2≤
      workCoefficient*(N+1)*size N (inputSize i)*RationalCostModel.schoolbook.rat (width N (inputSize i)) := by
  have hrows:=rows_cost i r hr
  rw [price_eq]
  unfold workCoefficient
  exact profile callbackCoefficient N (size N (inputSize i))
    (RationalCostModel.schoolbook.rat (width N (inputSize i))) (address N)
    (PlayerSpecificWidthExecution.run RationalCostModel.schoolbook (N+1)).2 (first i).2 (second i).2 (inverse r).2 (rows i r).2
    (PlayerSpecificRationalTrace.price RationalCostModel.schoolbook (PlayerSpecificAlgebraicInitialVectorExecution.frame i (inverse r).1))
    (size_bounds N (inputSize i)).1 (address_bounds N (inputSize i)).2.1 (measurement_cost i)
    (input_costs i).1 (input_costs i).2 (inverse_cost i r hr) hrows (frame_cost i r hr)

theorem polynomial_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    (PlayerSpecificAlgebraicInitialVectorExecution.run RationalCostModel.schoolbook i r).2≤
      polynomialCoefficient*(N+1)*size N (inputSize i)^3 := by
  have hc:=source_cost i r hr
  have hp:=PlayerSpecificFiniteParameterCost.schoolbook_profile workCoefficient widthCoefficient
    ((N+1)*size N (inputSize i)) (size N (inputSize i)) (size_bounds N (inputSize i)).1
  have hb : workCoefficient*(N+1)*size N (inputSize i)*RationalCostModel.schoolbook.rat (width N (inputSize i))≤
      polynomialCoefficient*(N+1)*size N (inputSize i)^3 := by
    unfold width polynomialCoefficient
    ring_nf at hp ⊢
    exact hp
  exact hc.trans hb

end Blotto.PlayerSpecificAlgebraicInitialVectorCost
