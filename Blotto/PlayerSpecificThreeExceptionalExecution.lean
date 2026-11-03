import Blotto.PlayerSpecificThreePreparationInputs

/-! The actual exceptional table computes its nine constant weights
once and materializes the original literal-zero endpoint arrays. -/
namespace Blotto.PlayerSpecificThreeExceptionalExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicThreeInput
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def programs : FixedArrayTable 9 (RationalExpression 5) :=
  FixedArrayTable.ofFn (fun slot => .literal (if slot=0 then 1 else 0))

def run (model : RationalCostModel) (root : Candidate) (a : Input) : Descriptor 3 9×ℕ :=
  let weights:=PlayerSpecificExpressionVectorExecution.run model root (PlayerSpecificThreeEnvironmentExecution.input a) programs
  let result:Descriptor 3 9:=⟨weights.1,FixedArrayTable.ofFn (fun _ => FixedArrayTable.ofFn ![[],[],a.budget]),
    FixedArrayTable.ofFn (fun _ => FixedArrayTable.ofFn ![a.first,a.second,[]])⟩
  (result,weights.2+price model (PlayerSpecificDescriptorProgramExecution.frame root (PlayerSpecificThreeEnvironmentExecution.input a) result))

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).1=PlayerSpecificAlgebraicOrderedThree.exceptional root a := by
  simp only [run,PlayerSpecificExpressionVectorExecution.value,programs,FixedArrayTable.read_ofFn,
    PlayerSpecificAlgebraicExpression.run,PlayerSpecificAlgebraicOrderedThree.exceptional]

theorem depth (j : Fin 9) : (programs.read j).depth≤0 := by
  simp only [programs,FixedArrayTable.read_ofFn]; split <;> decide
theorem literals (j : Fin 9) : (programs.read j).LiteralHeights 1 := by
  simp only [programs,FixedArrayTable.read_ofFn]; split
  · exact PlayerSpecificPolynomialHeights.one_height
  · exact PlayerSpecificPolynomialHeights.zero_height

end Blotto.PlayerSpecificThreeExceptionalExecution
