import Blotto.PlayerSpecificNestedFirstTableSourceCost

/-! A conditional family computes its one changed probability once
and prices all original/returned raw record fields and record packing. -/
namespace Blotto.PlayerSpecificNestedFamilyExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) (short : Data) : Input×ℕ :=
  let probability:=PlayerSpecificNestedParameterExecution.scalar model root a short 2
  let result:Input:=⟨a.budget,a.first,a.second,a.long,short,probability.1⟩
  (result,probability.2+price model (PlayerSpecificExpressionVectorExecution.frame root (environment a short) (environment result []))+
    price model (List.replicate 6 (.control 0)))

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (short : Data) :
    (run model root a short).1=PlayerSpecificAlgebraicNestedFamily.family model root a short := by
  simp only [run,PlayerSpecificNestedParameterExecution.scalar_value,PlayerSpecificAlgebraicNestedFamily.family]
theorem packing (model : RationalCostModel) : price model (List.replicate 6 (.control 0))=12 := rfl

theorem price_equation (model : RationalCostModel) (root : Candidate) (a : Input) (short : Data) :
    (run model root a short).2=(PlayerSpecificNestedParameterExecution.scalar model root a short 2).2+
      price model (PlayerSpecificExpressionVectorExecution.frame root (environment a short) (environment (run model root a short).1 []))+12 := by
  simp only [run,packing]

end Blotto.PlayerSpecificNestedFamilyExecution
