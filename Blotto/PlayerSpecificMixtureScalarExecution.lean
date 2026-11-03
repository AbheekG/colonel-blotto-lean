import Blotto.PlayerSpecificDescriptorPadSourceCost

/-! Binary mixtures retain their complement once and execute one
product for each original weight. Scalar return reads are also priced. -/
namespace Blotto.PlayerSpecificMixtureScalarExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def oneEnvironment (p : Data) : FixedArrayTable 1 Data := FixedArrayTable.ofFn (fun _ => p)
def twoEnvironment (p q : Data) : FixedArrayTable 2 Data := FixedArrayTable.ofFn ![p,q]
def complementPrograms : FixedArrayTable 1 (RationalExpression 1) :=
  FixedArrayTable.ofFn (fun _ => .sub (.literal 1) (.input 0))
def scalePrograms : FixedArrayTable 1 (RationalExpression 2) :=
  FixedArrayTable.ofFn (fun _ => .mul (.input 0) (.input 1))

def complement (model : RationalCostModel) (root : Candidate) (p : Data) : Data×ℕ :=
  let table:=PlayerSpecificExpressionVectorExecution.run model root (oneEnvironment p) complementPrograms
  (table.1.read 0,table.2+price model [.control 0])
def scale (model : RationalCostModel) (root : Candidate) (p q : Data) : Data×ℕ :=
  let table:=PlayerSpecificExpressionVectorExecution.run model root (twoEnvironment p q) scalePrograms
  (table.1.read 0,table.2+price model [.control 0])

theorem complement_value (model : RationalCostModel) (root : Candidate) (p : Data) :
    (complement model root p).1=PlayerSpecificAlgebraicField.minus root.polynomial
      (PlayerSpecificAlgebraicField.constant root.polynomial 1) p := by
  simp only [complement,PlayerSpecificExpressionVectorExecution.read_value,complementPrograms,
    oneEnvironment,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicExpression.run]
theorem scale_value (model : RationalCostModel) (root : Candidate) (p q : Data) :
    (scale model root p q).1=PlayerSpecificAlgebraicField.times root.polynomial p q := by
  simp [scale,PlayerSpecificExpressionVectorExecution.read_value,scalePrograms,
    twoEnvironment,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicExpression.run]

theorem complement_depth (j : Fin 1) : (complementPrograms.read j).depth≤1 := by
  rw [complementPrograms,FixedArrayTable.read_ofFn]; decide
theorem scale_depth (j : Fin 1) : (scalePrograms.read j).depth≤1 := by
  rw [scalePrograms,FixedArrayTable.read_ofFn]; decide
theorem complement_literals (j : Fin 1) (H : ℕ) (hH : 1≤H) : (complementPrograms.read j).LiteralHeights H := by
  rw [complementPrograms,FixedArrayTable.read_ofFn]
  exact ⟨PlayerSpecificPolynomialHeights.one_height.mono hH,trivial⟩
theorem scale_literals (j : Fin 1) (H : ℕ) : (scalePrograms.read j).LiteralHeights H := by
  rw [scalePrograms,FixedArrayTable.read_ofFn]
  trivial
theorem complement_operations : PlayerSpecificExpressionVectorExecution.operations complementPrograms=3 := by decide
theorem scale_operations : PlayerSpecificExpressionVectorExecution.operations scalePrograms=3 := by decide
theorem packing (model : RationalCostModel) : price model [.control 0]=2 := rfl

end Blotto.PlayerSpecificMixtureScalarExecution
