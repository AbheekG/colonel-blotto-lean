import Blotto.PlayerSpecificNestedPositiveSourceCost

/-! The conditional zero corner materializes each literal weight once
and copies the actual raw endpoints, including the reached extra row. -/
namespace Blotto.PlayerSpecificNestedZeroExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def programs : FixedArrayTable 9 (RationalExpression 7) :=
  FixedArrayTable.ofFn (fun slot => .literal (if slot=0 then 1 else 0))

def run (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) : Descriptor 3 9×ℕ :=
  let weights:=PlayerSpecificExpressionVectorExecution.run model root (environment a extra) programs
  let result:Descriptor 3 9:=⟨weights.1,FixedArrayTable.ofFn (fun _ => FixedArrayTable.ofFn ![[],a.second,extra]),
    FixedArrayTable.ofFn (fun _ => FixedArrayTable.ofFn ![a.first,[],extra])⟩
  (result,weights.2+price model (PlayerSpecificDescriptorProgramExecution.frame root (environment a extra) result))

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (extra : Data) :
    (run model root a extra).1=PlayerSpecificAlgebraicNestedFirstTable.zero root a extra := by
  simp only [run,PlayerSpecificExpressionVectorExecution.value,programs,FixedArrayTable.read_ofFn,
    PlayerSpecificAlgebraicExpression.run,PlayerSpecificAlgebraicNestedFirstTable.zero]

theorem depth (j : Fin 9) : (programs.read j).depth≤0 := by
  simp only [programs,FixedArrayTable.read_ofFn]; split <;> decide
theorem literals (j : Fin 9) : (programs.read j).LiteralHeights 1 := by
  simp only [programs,FixedArrayTable.read_ofFn]; split
  · exact PlayerSpecificPolynomialHeights.one_height
  · exact PlayerSpecificPolynomialHeights.zero_height

end Blotto.PlayerSpecificNestedZeroExecution
