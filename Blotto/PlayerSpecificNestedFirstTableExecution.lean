import Blotto.PlayerSpecificNestedGeometrySourceCost

/-! The first nested conditional table executes its test once and
only its selected positive-geometry or zero-corner continuation. -/
namespace Blotto.PlayerSpecificNestedFirstTableExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) : Descriptor 3 9×ℕ :=
  let tested:=PlayerSpecificNestedPositiveExecution.run model root a extra
  let result:=if tested.1 then PlayerSpecificNestedGeometryExecution.run model root a extra
    else PlayerSpecificNestedZeroExecution.run model root a extra
  (result.1,tested.2+result.2+price model [.control 1])

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) :
    (run model root a extra).1=PlayerSpecificAlgebraicNestedFirstTable.prepare model root a extra := by
  simp only [run,PlayerSpecificNestedPositiveExecution.value,PlayerSpecificAlgebraicNestedFirstTable.prepare]
  split <;> simp_all only [PlayerSpecificNestedGeometryExecution.value,PlayerSpecificNestedZeroExecution.value]

theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl

end Blotto.PlayerSpecificNestedFirstTableExecution
