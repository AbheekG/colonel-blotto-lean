import Blotto.PlayerSpecificFourReflectedTerminalSourceCost

/-! Three cached subtraction traces and the literal zero fourth row
implement the native reflected allocation. -/
namespace Blotto.PlayerSpecificReflectAppendExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def environment (long y : FixedArrayTable 3 Data) : FixedArrayTable 6 Data := FixedArrayTable.ofFn
  ![long.read 0,long.read 1,long.read 2,y.read 0,y.read 1,y.read 2]
def packing : Trace := List.replicate 8 (.control 1)

def run (model : RationalCostModel) (root : Candidate) (long y : FixedArrayTable 3 Data) :
    FixedArrayTable 4 Data×ℕ :=
  let first:=PlayerSpecificFieldCombination.run true root.polynomial (long.read 0) (y.read 0)
  let second:=PlayerSpecificFieldCombination.run true root.polynomial (long.read 1) (y.read 1)
  let third:=PlayerSpecificFieldCombination.run true root.polynomial (long.read 2) (y.read 2)
  let result:=FixedArrayTable.ofFn ![first.1,second.1,third.1,[]]
  (result,price model first.2+price model second.2+price model third.2+
    price model (PlayerSpecificExpressionVectorExecution.frame root (environment long y) result)+
    price model packing)

theorem value (model : RationalCostModel) (root : Candidate) (long y : FixedArrayTable 3 Data) :
    (run model root long y).1=PlayerSpecificAlgebraicReflectAppend.reflect root long y := by
  simp only [run,PlayerSpecificFieldCombination.value,ite_true,
    PlayerSpecificAlgebraicReflectAppend.reflect]

theorem packing_cost (model : RationalCostModel) : price model packing=16 := rfl

theorem price_equation (model : RationalCostModel) (root : Candidate) (long y : FixedArrayTable 3 Data) :
    (run model root long y).2=
      price model (PlayerSpecificFieldCombination.run true root.polynomial (long.read 0) (y.read 0)).2+
      price model (PlayerSpecificFieldCombination.run true root.polynomial (long.read 1) (y.read 1)).2+
      price model (PlayerSpecificFieldCombination.run true root.polynomial (long.read 2) (y.read 2)).2+
      price model (PlayerSpecificExpressionVectorExecution.frame root (environment long y) (run model root long y).1)+16 := by
  simp only [run,packing_cost]

end Blotto.PlayerSpecificReflectAppendExecution
