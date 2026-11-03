import Blotto.PlayerSpecificNestedInteriorDrawSourceCost

/-! A closed-probability endpoint materializes its five actual input
fields once, including the one literal probability and selected length. -/
namespace Blotto.PlayerSpecificNestedEndpointInputExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def programs (useShort : Bool) : FixedArrayTable 5 (RationalExpression 7) :=
  FixedArrayTable.ofFn ![.input 0,.input 1,.input 2,.input (if useShort then 4 else 3),.literal 1]

def run (model : RationalCostModel) (root : Candidate) (a : Input) (useShort : Bool) : PlayerSpecificAlgebraicThreeInput.Input×ℕ :=
  let fields:=PlayerSpecificExpressionVectorExecution.run model root (environment a []) (programs useShort)
  (⟨fields.1.read 0,fields.1.read 1,fields.1.read 2,fields.1.read 3,fields.1.read 4⟩,
    fields.2+price model (List.replicate 6 (.control 1)))

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (useShort : Bool) :
    (run model root a useShort).1=PlayerSpecificAlgebraicNestedSpecInput.endpoint root a useShort := by
  cases useShort <;> simp [run,PlayerSpecificExpressionVectorExecution.read_value,programs,environment,FixedArrayTable.read_ofFn,
    PlayerSpecificAlgebraicExpression.run,PlayerSpecificAlgebraicNestedSpecInput.endpoint]
theorem depth (useShort : Bool) (j : Fin 5) : ((programs useShort).read j).depth≤0 := by
  cases useShort <;> fin_cases j <;> decide
theorem literals (useShort : Bool) (j : Fin 5) (H : ℕ) (hH : 1≤H) : ((programs useShort).read j).LiteralHeights H := by
  fin_cases j <;> simp [programs,FixedArrayTable.read_ofFn,RationalExpression.LiteralHeights]
  exact PlayerSpecificPolynomialHeights.one_height.mono hH
theorem operations (useShort : Bool) : PlayerSpecificExpressionVectorExecution.operations (programs useShort)=5 := by
  cases useShort <;> decide
theorem packing (model : RationalCostModel) : price model (List.replicate 6 (.control 1))=12 := rfl

end Blotto.PlayerSpecificNestedEndpointInputExecution
