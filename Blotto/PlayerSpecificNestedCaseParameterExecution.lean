import Blotto.PlayerSpecificFourParameterSourceCost

/-! Actual nested case parameters retain one residual environment and
one execution of each requested scalar. Original and returned record
rows, finite index reads and fixed record packing are priced. -/
namespace Blotto.PlayerSpecificNestedCaseParameterExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedCaseParameters
set_option autoImplicit false
set_option maxHeartbeats 2500000

def fields (p : Prepared) : FixedArrayTable 6 Data := FixedArrayTable.ofFn ![p.u,p.v,p.h,p.mirror,p.secondAlpha,p.thirdAlpha]
def frame (root : Candidate) (a : Input) (p : Prepared) : Trace :=
  PlayerSpecificExpressionVectorExecution.frame root (environment a []) (fields p)

def run (model : RationalCostModel) (root : Candidate) (a : Input) : Prepared×ℕ :=
  let geometry:=PlayerSpecificResidualEnvironmentExecution.run model root a
  let mirror:=PlayerSpecificNestedParameterExecution.scalar model root a [] 3
  let second:=PlayerSpecificNestedParameterExecution.scalar model root a [] 4
  let third:=PlayerSpecificNestedParameterExecution.scalar model root a [] 5
  let result:Prepared:=⟨geometry.1.read 0,geometry.1.read 1,geometry.1.read 3,mirror.1,second.1,third.1⟩
  (result,geometry.2+mirror.2+second.2+third.2+price model (frame root a result)+price model (List.replicate 10 (.control 1)))

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).1=PlayerSpecificAlgebraicNestedCaseParameters.prepare model root a := by
  simp only [run,PlayerSpecificResidualEnvironmentExecution.value,PlayerSpecificNestedParameterExecution.scalar_value,
    PlayerSpecificAlgebraicNestedCaseParameters.prepare,PlayerSpecificAlgebraicNestedInput.scalar]

theorem packing (model : RationalCostModel) : price model (List.replicate 10 (.control 1))=20 := rfl

end Blotto.PlayerSpecificNestedCaseParameterExecution
