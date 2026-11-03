import Blotto.PlayerSpecificRecognitionScanCost

/-! Complete priced scan of the actual rational input's cells, with exact
same return/rejection and a polynomial bound in original encoded input.
Constructing the sorted rational cell list remains a separate caller. -/
namespace Blotto.PlayerSpecificRecognitionScanContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificRecognitionScanExecution
set_option autoImplicit false
set_option maxHeartbeats 2500000

def inputSize {n : ℕ} (i : RationalPlayerSpecificInput n) : ℕ := PlayerSpecificRecognitionInputHeights.inputHeight i
def cellHeight (n L : ℕ) : ℕ := PlayerSpecificRecognitionInputHeights.cellHeight n L
def widthCoefficient : ℕ := 12*PlayerSpecificRecognitionScanBudget.widthCoefficient
def workCoefficient : ℕ := 44*PlayerSpecificFiniteCellBudget.workCoefficient+2000
def polynomialCoefficient : ℕ := workCoefficient*(widthCoefficient*widthCoefficient+widthCoefficient)

theorem profiles (C D n L : ℕ) :
    (2*(C*(10*(n+1)*(L+1)+1))+500*((n+1)+1))*((n+1)+1)≤(44*C+2000)*(n+1)^2*(L+1) ∧
      D*((n+1)+10*(n+1)*(L+1)+1)≤(12*D)*((n+1)*(L+1)) := by
  have hcell : 10*(n+1)*(L+1)+1≤11*(n+1)*(L+1) := by nlinarith
  have hn : n+2≤2*(n+1)*(L+1) := by nlinarith
  have hunit : 2*(C*(10*(n+1)*(L+1)+1))+500*((n+1)+1)≤(22*C+1000)*((n+1)*(L+1)) := by
    have hm:=Nat.mul_le_mul_left (2*C) hcell
    have hh:=Nat.mul_le_mul_left 500 hn
    nlinarith only [hm,hh]
  have hwork:=Nat.mul_le_mul hunit (show (n+1)+1≤2*(n+1) by omega)
  have hwidth : (n+1)+10*(n+1)*(L+1)+1≤12*((n+1)*(L+1)) := by nlinarith
  refine ⟨by nlinarith only [hwork],?_⟩
  exact (Nat.mul_le_mul_left D hwidth).trans_eq (by ring)

theorem source_cost {n : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput n) :
    (run model i.budget (PlayerSpecificRationalIntervals.run i)).2≤
      workCoefficient*(n+1)^2*(inputSize i+1)*model.rat (widthCoefficient*((n+1)*(inputSize i+1))) := by
  have hinput:=PlayerSpecificRecognitionInputHeights.original_fields i
  have hlarge : inputSize i≤cellHeight n (inputSize i) ∧ 1≤cellHeight n (inputSize i) := by
    unfold cellHeight PlayerSpecificRecognitionInputHeights.cellHeight
    constructor <;> nlinarith
  have hcount:=PlayerSpecificRationalIntervals.count i
  have hcst:=PlayerSpecificRecognitionScanCost.source_cost model i.budget (PlayerSpecificRationalIntervals.run i)
    (n+1) (cellHeight n (inputSize i)) (hinput.1.mono hlarge.1) hlarge.2 (by omega)
    (PlayerSpecificRecognitionInputHeights.cells i) (PlayerSpecificRationalIntervals.cubic_nonzero i)
  rw [hcount] at hcst
  have hp:=profiles PlayerSpecificFiniteCellBudget.workCoefficient PlayerSpecificRecognitionScanBudget.widthCoefficient n (inputSize i)
  exact hcst.trans (Nat.mul_le_mul hp.1 (model.monotone hp.2))

theorem actual_contract {n : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput n) :
    let result:=run model i.budget (PlayerSpecificRationalIntervals.run i)
    result.1=PlayerSpecificFiniteRecognition.run model i ∧
      (result.1=none ↔ ¬∃ gamma sigma,PlayerSpecificRecognition.ValidParameters
        i.valuesA.values i.valuesB.values (i.budget:ℝ) gamma sigma) ∧
      result.2≤workCoefficient*(n+1)^2*(inputSize i+1)*model.rat (widthCoefficient*((n+1)*(inputSize i+1))) := by
  have hv:=value model i.budget i.budget_pos.ne' (PlayerSpecificRationalIntervals.run i)
  refine ⟨hv,?_,source_cost model i⟩
  rw [hv]
  exact PlayerSpecificFiniteRecognitionComplete.rejection_iff model i

theorem polynomial_cost {n : ℕ} (i : RationalPlayerSpecificInput n) :
    (run RationalCostModel.schoolbook i.budget (PlayerSpecificRationalIntervals.run i)).2≤
      polynomialCoefficient*(n+1)*((n+1)*(inputSize i+1))^3 := by
  have hc:=source_cost RationalCostModel.schoolbook i
  have hp:=PlayerSpecificRootContract.schoolbook_profile workCoefficient widthCoefficient
    ((n+1)*(inputSize i+1)) (by
      have hm:=Nat.mul_le_mul (show 1≤n+1 by omega) (show 1 ≤ inputSize i+1 by omega)
      simpa only [Nat.one_mul] using hm)
  have hm:=Nat.mul_le_mul_left (n+1) hp
  change (run RationalCostModel.schoolbook i.budget (PlayerSpecificRationalIntervals.run i)).2≤
    workCoefficient*(n+1)^2*(inputSize i+1)*
      ((widthCoefficient*((n+1)*(inputSize i+1)))*(widthCoefficient*((n+1)*(inputSize i+1)))+
        widthCoefficient*((n+1)*(inputSize i+1))) at hc
  apply hc.trans
  unfold polynomialCoefficient
  convert hm using 1 <;> ring

end Blotto.PlayerSpecificRecognitionScanContract
