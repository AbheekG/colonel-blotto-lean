import Blotto.PlayerSpecificThreeEnvironmentSourceCost

/-! Measured overlap formulas retain all nine row results. The fixed
return packing has its own three control events. -/
namespace Blotto.PlayerSpecificOverlapRowExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def weights : FixedArrayTable 1 (RationalExpression 16) := FixedArrayTable.ofFn (fun _ => OverlapFormulaCode.weight)
def first : FixedArrayTable 1 (FixedArrayTable 4 (RationalExpression 16)) := FixedArrayTable.ofFn (fun _ => FixedArrayTable.ofFn OverlapFormulaCode.safeP)
def second : FixedArrayTable 1 (FixedArrayTable 4 (RationalExpression 16)) := FixedArrayTable.ofFn (fun _ => FixedArrayTable.ofFn OverlapFormulaCode.safeQ)

def run (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 16 Data) :
    (Data×(FixedArrayTable 4 Data×FixedArrayTable 4 Data))×ℕ :=
  let d:=PlayerSpecificDescriptorProgramExecution.run model root env weights first second
  ((d.1.weights.read 0,(d.1.first.read 0,d.1.second.read 0)),d.2+price model [.control 0,.control 0,.control 0])

theorem value (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 16 Data) :
    (run model root env).1=PlayerSpecificAlgebraicOverlapTable.row model root env := by
  simp only [run,PlayerSpecificDescriptorProgramExecution.value,weights,first,second,FixedArrayTable.read_ofFn,
    PlayerSpecificAlgebraicOverlapTable.row]

def operationCount : ℕ := PlayerSpecificDescriptorProgramExecution.operations weights first second
theorem packing (model : RationalCostModel) : price model [.control 0,.control 0,.control 0]=6 := by rfl

end Blotto.PlayerSpecificOverlapRowExecution
