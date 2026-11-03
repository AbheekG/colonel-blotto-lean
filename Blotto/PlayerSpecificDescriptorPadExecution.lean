import Blotto.PlayerSpecificDescriptorShiftSourceCost

/-! Padding materializes zero weights and copied feasible endpoints.
Both descriptor arrays, their indices, and the fallback read are priced. -/
namespace Blotto.PlayerSpecificDescriptorPadExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def environment : FixedArrayTable 0 Data := FixedArrayTable.ofFn Fin.elim0

def run {N k : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N k) (m : ℕ) (fallback : Fin k) : Descriptor N (k+m)×ℕ :=
  let result:=PlayerSpecificAlgebraicDescriptorPad.pad d m fallback
  (result,price model (PlayerSpecificDescriptorProgramExecution.frame root environment d)+
    price model (PlayerSpecificDescriptorProgramExecution.frame root environment result)+
    price model [.control fallback.val,.control 0,.control 0,.control 0])

theorem value {N k : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N k) (m : ℕ) (fallback : Fin k) :
    (run model root d m fallback).1=PlayerSpecificAlgebraicDescriptorPad.pad d m fallback := rfl

theorem packing_cost {k : ℕ} (model : RationalCostModel) (fallback : Fin k) :
    price model [.control fallback.val,.control 0,.control 0,.control 0]≤2*(k+1)+6 := by
  simp only [price,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Event.price]
  have h0 : binaryWordWidth 0=1 := by decide
  rw [h0]
  have h:=control_width fallback.val
  have hj:=fallback.isLt
  omega

end Blotto.PlayerSpecificDescriptorPadExecution
