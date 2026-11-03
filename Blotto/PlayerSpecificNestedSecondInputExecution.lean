import Blotto.PlayerSpecificCompareSourceCost

/-! The second uniform component computes its reduced budget and
length once and retains the five actual returned input fields. -/
namespace Blotto.PlayerSpecificNestedSecondInputExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def environment (a : Input) (p : Prepared) : FixedArrayTable 5 Data :=
  FixedArrayTable.ofFn ![a.budget,a.first,a.second,a.short,p.mirror]
def programs : FixedArrayTable 5 (RationalExpression 5) :=
  FixedArrayTable.ofFn ![.sub (.input 0) (.input 4),.input 1,.input 2,.sub (.input 3) (.input 4),.literal 1]

def run (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) : PlayerSpecificAlgebraicThreeInput.Input×ℕ :=
  let fields:=PlayerSpecificExpressionVectorExecution.run model root (environment a p) programs
  (⟨fields.1.read 0,fields.1.read 1,fields.1.read 2,fields.1.read 3,fields.1.read 4⟩,
    fields.2+price model (List.replicate 5 (.control 0)))

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) :
    (run model root a p).1=PlayerSpecificAlgebraicNestedSecondUniform.input root a p := by
  simp [run,PlayerSpecificExpressionVectorExecution.read_value,environment,programs,FixedArrayTable.read_ofFn,
    PlayerSpecificAlgebraicExpression.run,PlayerSpecificAlgebraicNestedSecondUniform.input]
theorem depth (j : Fin 5) : (programs.read j).depth≤1 := by fin_cases j <;> decide
theorem literals (j : Fin 5) (H : ℕ) (hH : 1≤H) : (programs.read j).LiteralHeights H := by
  fin_cases j <;> simp [programs,FixedArrayTable.read_ofFn,RationalExpression.LiteralHeights]
  exact PlayerSpecificPolynomialHeights.one_height.mono hH
theorem packing (model : RationalCostModel) : price model (List.replicate 5 (.control 0))=10 := rfl

end Blotto.PlayerSpecificNestedSecondInputExecution
