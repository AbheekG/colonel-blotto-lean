import Blotto.PlayerSpecificOverlapTableSourceCost

/-! Both gluing parent inputs materialize five fields from the retained
raw input and shared eight-parameter table. Each field executes once. -/
namespace Blotto.PlayerSpecificFourParentInputExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def environment (a : Input) (p : FixedArrayTable 8 Data) : FixedArrayTable 14 Data :=
  FixedArrayTable.ofFn (fun j => Fin.addCases (m:=6) (n:=8)
    (fun i => (PlayerSpecificAlgebraicFourInput.environment a).read i) (fun i => p.read i) j)
def programs (useSecond : Bool) : FixedArrayTable 5 (RationalExpression 14) :=
  if useSecond then FixedArrayTable.ofFn ![.input 9,.input 7,.input 3,.input 4,.input 5]
  else FixedArrayTable.ofFn ![.input 8,.input 1,.input 2,.input 7,.literal 1]

def run (model : RationalCostModel) (root : Candidate) (a : Input) (p : FixedArrayTable 8 Data) (useSecond : Bool) :
    PlayerSpecificAlgebraicThreeInput.Input×ℕ :=
  let fields:=PlayerSpecificExpressionVectorExecution.run model root (environment a p) (programs useSecond)
  (⟨fields.1.read 0,fields.1.read 1,fields.1.read 2,fields.1.read 3,fields.1.read 4⟩,
    fields.2+price model (List.replicate 6 (.control 1)))

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (p : FixedArrayTable 8 Data) (useSecond : Bool) :
    (run model root a p useSecond).1=if useSecond then PlayerSpecificAlgebraicFourGluingInputs.second a p
      else PlayerSpecificAlgebraicFourGluingInputs.first root a p := by
  cases useSecond <;> simp [run,PlayerSpecificExpressionVectorExecution.read_value,programs,environment,
    PlayerSpecificAlgebraicFourInput.environment,FixedArrayTable.read_ofFn,Fin.addCases,PlayerSpecificAlgebraicExpression.run,
    PlayerSpecificAlgebraicFourGluingInputs.first,PlayerSpecificAlgebraicFourGluingInputs.second]
theorem depth (b : Bool) (j : Fin 5) : ((programs b).read j).depth≤0 := by
  cases b <;> fin_cases j <;> decide
theorem literals (b : Bool) (j : Fin 5) (H : ℕ) (hH : 1≤H) : ((programs b).read j).LiteralHeights H := by
  cases b <;> fin_cases j <;> simp [programs,FixedArrayTable.read_ofFn,RationalExpression.LiteralHeights]
  exact PlayerSpecificPolynomialHeights.one_height.mono hH
theorem operations (b : Bool) : PlayerSpecificExpressionVectorExecution.operations (programs b)=5 := by cases b <;> decide
theorem packing (model : RationalCostModel) : price model (List.replicate 6 (.control 1))=12 := rfl

end Blotto.PlayerSpecificFourParentInputExecution
