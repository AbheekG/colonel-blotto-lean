import Blotto.PlayerSpecificNestedFirstProfileSourceCost

/-! The third profile retains its residual table once and constructs
the conditional family only when the reached length is positive. -/
namespace Blotto.PlayerSpecificNestedThirdProfileExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def residual (model : RationalCostModel) (root : Candidate) (a : Input) : Descriptor 3 9×ℕ :=
  let table:=PlayerSpecificResidualTableExecution.run model root a
  let padded:=PlayerSpecificDescriptorPadExecution.run model root table.1 6 0
  (padded.1,table.2+padded.2+price model [.control 1])
def positive (model : RationalCostModel) (root : Candidate) (p : Prepared) : Bool×ℕ :=
  let tested:=PlayerSpecificAlgebraicComparisonExecution.run model root p.v []
  (!tested.1,tested.2+price model [.control 1])
def run (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (K : ℕ) (outer : Fin K → Bool) : Descriptor 3 18×ℕ :=
  let r:=residual model root a
  let tested:=positive model root p
  let result:=if tested.1 then
    let f:=PlayerSpecificNestedProfileExecution.run model root a p.v K outer
    let joined:=PlayerSpecificDescriptorBinaryExecution.run model root p.thirdAlpha f.1 r.1
    (joined.1,f.2+joined.2)
  else PlayerSpecificDescriptorPadExecution.run model root r.1 9 0
  (result.1,r.2+tested.2+result.2+price model [.control 1])

theorem residual_value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (residual model root a).1=PlayerSpecificAlgebraicNestedThirdProfile.residual model root a := by
  simp only [residual,PlayerSpecificResidualTableExecution.value,PlayerSpecificDescriptorPadExecution.value,
    PlayerSpecificAlgebraicNestedThirdProfile.residual]
theorem positive_value (model : RationalCostModel) (root : Candidate) (p : Prepared) :
    (positive model root p).1=PlayerSpecificAlgebraicNestedThirdProfile.positive model root p := by
  simp only [positive,PlayerSpecificAlgebraicComparisonExecution.value,PlayerSpecificAlgebraicNestedThirdProfile.positive]
theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (K : ℕ) (outer : Fin K → Bool) :
    (run model root a p K outer).1=PlayerSpecificAlgebraicNestedThirdProfile.prepare model root a p K outer := by
  simp only [run,residual_value,positive_value,PlayerSpecificAlgebraicNestedThirdProfile.prepare]
  split <;> simp_all only [PlayerSpecificNestedProfileExecution.value,PlayerSpecificDescriptorBinaryExecution.value,PlayerSpecificDescriptorPadExecution.value]
theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl

theorem residual_price (model : RationalCostModel) (root : Candidate) (a : Input) :
    (residual model root a).2=(PlayerSpecificResidualTableExecution.run model root a).2+
      (PlayerSpecificDescriptorPadExecution.run model root (PlayerSpecificAlgebraicResidualTable.prepare model root a) 6 0).2+2 := by
  simp only [residual,PlayerSpecificResidualTableExecution.value,packing]
theorem positive_price (model : RationalCostModel) (root : Candidate) (p : Prepared) :
    (positive model root p).2=(PlayerSpecificAlgebraicComparisonExecution.run model root p.v []).2+2 := by
  simp only [positive,packing]

end Blotto.PlayerSpecificNestedThirdProfileExecution
