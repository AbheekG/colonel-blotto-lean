import Blotto.PlayerSpecificFourGluingSourceCost

/-! Complete normal four-variable draw retains its gluing table once
and passes it directly to the complete measured segment sampler. -/
namespace Blotto.PlayerSpecificFourGluingDrawExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ) (bits : Fin (80*H+K) → Bool) : FixedArrayTable 4 Data×ℕ :=
  let table:=PlayerSpecificFourGluingExecution.run model root a
  let result:=PlayerSpecificSegmentDrawExecution.run model root table.1 80 H K bits
  (result.1,table.2+result.2+price model [.control 1])
theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ) (bits : Fin (80*H+K) → Bool) :
    (run model root a H K bits).1=PlayerSpecificAlgebraicFourGluingDraw.draw model root a H K bits := by
  simp only [run,PlayerSpecificFourGluingExecution.value,PlayerSpecificSegmentDrawExecution.value,PlayerSpecificAlgebraicFourGluingDraw.draw]
theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl
theorem price_equation (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ) (bits : Fin (80*H+K) → Bool) :
    (run model root a H K bits).2=(PlayerSpecificFourGluingExecution.run model root a).2+
      (PlayerSpecificSegmentDrawExecution.run model root (PlayerSpecificAlgebraicFourGluingTable.prepare model root a) 80 H K bits).2+2 := by
  simp only [run,PlayerSpecificFourGluingExecution.value,packing]

end Blotto.PlayerSpecificFourGluingDrawExecution
