import Blotto.PlayerSpecificThreeDrawSourceCost

/-! Actual measured nested scalar and first-geometry programs share
the native seven-row input environment. Only the requested scalar runs. -/
namespace Blotto.PlayerSpecificNestedParameterExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def scalarProgram (j : Fin 6) : FixedArrayTable 1 (RationalExpression 7) :=
  FixedArrayTable.ofFn (fun _ => RationalNestedParametersCode.scalarPrograms j)
def firstPrograms : FixedArrayTable 4 (RationalExpression 7) := FixedArrayTable.ofFn RationalNestedParametersCode.firstParameters

def scalar (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) (j : Fin 6) : Data×ℕ :=
  let result:=PlayerSpecificExpressionVectorExecution.run model root (environment a extra) (scalarProgram j)
  (result.1.read 0,result.2+price model [.control j.val,.control 0])

def firstEnvironment (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) : FixedArrayTable 4 Data×ℕ :=
  PlayerSpecificExpressionVectorExecution.run model root (environment a extra) firstPrograms

theorem scalar_value (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) (j : Fin 6) :
    (scalar model root a extra j).1=PlayerSpecificAlgebraicNestedInput.scalar model root a extra j := by
  simp only [scalar,PlayerSpecificExpressionVectorExecution.read_value,scalarProgram,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicNestedInput.scalar]

theorem first_value (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) :
    (firstEnvironment model root a extra).1=PlayerSpecificAlgebraicNestedInput.firstEnvironment model root a extra := by
  simp only [firstEnvironment,PlayerSpecificExpressionVectorExecution.value,firstPrograms,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicNestedInput.firstEnvironment]

theorem scalar_operations (j : Fin 6) : PlayerSpecificExpressionVectorExecution.operations (scalarProgram j)=
    (RationalNestedParametersCode.scalarPrograms j).operationBound := by
  simp [PlayerSpecificExpressionVectorExecution.operations,scalarProgram,FixedArrayTable.read_ofFn]

theorem packing_cost (model : RationalCostModel) (j : Fin 6) : price model [.control j.val,.control 0]≤9 := by
  simp only [price,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Event.price]
  have h0 : binaryWordWidth 0=1 := by decide
  rw [h0]
  have hj:=j.isLt
  have hb:=control_width j.val
  omega

end Blotto.PlayerSpecificNestedParameterExecution
