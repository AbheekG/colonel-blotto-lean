import Blotto.PlayerSpecificNestedThirdProfileSourceCost

/-! The second profile retains its family and exact strict mirror
test once. The uniform component executes only on the strict branch. -/
namespace Blotto.PlayerSpecificNestedSecondProfileExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def strict (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) : Bool×ℕ :=
  let tested:=PlayerSpecificAlgebraicComparisonExecution.run model root a.short p.mirror
  (!tested.1,tested.2+price model [.control 1])
def run (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (K : ℕ) (outer : Fin K → Bool) : Descriptor 3 18×ℕ :=
  let f:=PlayerSpecificNestedProfileExecution.run model root a p.mirror K outer
  let tested:=strict model root a p
  let result:=if tested.1 then
    let uniform:=PlayerSpecificNestedSecondUniformExecution.run model root a p
    let joined:=PlayerSpecificDescriptorBinaryExecution.run model root p.secondAlpha f.1 uniform.1
    (joined.1,uniform.2+joined.2)
  else PlayerSpecificDescriptorPadExecution.run model root f.1 9 0
  (result.1,f.2+tested.2+result.2+price model [.control 1])

theorem strict_value (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) :
    (strict model root a p).1=PlayerSpecificAlgebraicNestedSecondProfile.strict model root a p := by
  simp only [strict,PlayerSpecificAlgebraicComparisonExecution.value,PlayerSpecificAlgebraicNestedSecondProfile.strict]
theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (K : ℕ) (outer : Fin K → Bool) :
    (run model root a p K outer).1=PlayerSpecificAlgebraicNestedSecondProfile.prepare model root a p K outer := by
  simp only [run,PlayerSpecificNestedProfileExecution.value,strict_value,PlayerSpecificAlgebraicNestedSecondProfile.prepare]
  split <;> simp_all only [PlayerSpecificNestedSecondUniformExecution.value,PlayerSpecificDescriptorBinaryExecution.value,PlayerSpecificDescriptorPadExecution.value]
theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl
theorem strict_price (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) :
    (strict model root a p).2=(PlayerSpecificAlgebraicComparisonExecution.run model root a.short p.mirror).2+2 := by
  simp only [strict,packing]

end Blotto.PlayerSpecificNestedSecondProfileExecution
