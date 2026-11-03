import Blotto.PlayerSpecificSegmentSelectionEntryCost

/-! Actual measured affine-coordinate interpolation over cached left
and right scalar rows. Input and result arrays are fully priced. -/
namespace Blotto.PlayerSpecificInterpolationCoordinateExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def expression : RationalExpression 4 := .add (.mul (.input 0) (.input 2)) (.mul (.input 1) (.input 3))
def programs : FixedArrayTable 1 (RationalExpression 4) := FixedArrayTable.ofFn (fun _ => expression)
def environment (left right first second : Data) : FixedArrayTable 4 Data := FixedArrayTable.ofFn ![left,right,first,second]

def run (model : RationalCostModel) (root : Candidate) (left right first second : Data) : Data×ℕ :=
  let row:=PlayerSpecificExpressionVectorExecution.run model root (environment left right first second) programs
  (row.1.read 0,row.2+price model [.control 0])

theorem value (model : RationalCostModel) (root : Candidate) (left right first second : Data) :
    (run model root left right first second).1=PlayerSpecificAlgebraicField.plus root.polynomial
      (PlayerSpecificAlgebraicField.times root.polynomial left first) (PlayerSpecificAlgebraicField.times root.polynomial right second) := by
  simp [run,PlayerSpecificExpressionVectorExecution.read_value,programs,expression,environment,FixedArrayTable.read_ofFn,
    PlayerSpecificAlgebraicExpression.run]

theorem depth (j : Fin 1) : (programs.read j).depth≤2 := by
  rw [programs,FixedArrayTable.read_ofFn]
  decide
theorem literals (j : Fin 1) (H : ℕ) : (programs.read j).LiteralHeights H := by
  simp only [programs,FixedArrayTable.read_ofFn,expression,RationalExpression.LiteralHeights,true_and]
theorem operations : PlayerSpecificExpressionVectorExecution.operations programs=7 := by decide
theorem packing (model : RationalCostModel) : price model [.control 0]=2 := rfl

end Blotto.PlayerSpecificInterpolationCoordinateExecution
