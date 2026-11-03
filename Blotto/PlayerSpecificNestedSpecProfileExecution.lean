import Blotto.PlayerSpecificNestedSortedProfileSourceCost

/-! Closed-probability dispatch tests zero once, then tests one only
when reached. Exactly one endpoint or sorted interior profile executes. -/
namespace Blotto.PlayerSpecificNestedSpecProfileExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def qOne (model : RationalCostModel) (root : Candidate) (a : Input) : Bool×ℕ :=
  let one:=PlayerSpecificFieldCombinationContract.constant root.polynomial 1
  let tested:=PlayerSpecificAlgebraicComparisonExecution.run model root one.1 a.probability
  (tested.1,price model one.2+tested.2+price model [.control 1])
def run (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) : Descriptor 3 18×ℕ :=
  let zero:=PlayerSpecificAlgebraicComparisonExecution.run model root a.probability []
  if zero.1 then
    let result:=PlayerSpecificNestedEndpointProfileExecution.run model root a false
    (result.1,zero.2+result.2+price model [.control 1])
  else
    let one:=qOne model root a
    let result:=if one.1 then PlayerSpecificNestedEndpointProfileExecution.run model root a true
      else PlayerSpecificNestedSortedProfileExecution.run model root a K outer
    (result.1,zero.2+one.2+result.2+price model [.control 1,.control 1])

theorem qOne_value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (qOne model root a).1=PlayerSpecificAlgebraicNestedSpecProfile.qOne model root a := by
  simp only [qOne,PlayerSpecificFieldCombinationContract.constant_value,PlayerSpecificAlgebraicComparisonExecution.value,
    PlayerSpecificAlgebraicNestedSpecProfile.qOne]
theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) :
    (run model root a K outer).1=PlayerSpecificAlgebraicNestedSpecProfile.prepare model root a K outer := by
  simp only [run,PlayerSpecificAlgebraicComparisonExecution.value,qOne_value,
    PlayerSpecificAlgebraicNestedSpecProfile.prepare,PlayerSpecificAlgebraicNestedSpecProfile.qZero]
  split
  · simp_all only [PlayerSpecificNestedEndpointProfileExecution.value,ite_true]
  · split <;> simp_all only [PlayerSpecificNestedEndpointProfileExecution.value,PlayerSpecificNestedSortedProfileExecution.value]
theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl
theorem two_tests_packing (model : RationalCostModel) : price model [.control 1,.control 1]=4 := rfl
theorem qOne_price (model : RationalCostModel) (root : Candidate) (a : Input) :
    (qOne model root a).2=price model (PlayerSpecificFieldCombinationContract.constant root.polynomial 1).2+
      (PlayerSpecificAlgebraicComparisonExecution.run model root (PlayerSpecificAlgebraicField.constant root.polynomial 1) a.probability).2+2 := by
  simp only [qOne,PlayerSpecificFieldCombinationContract.constant_value,packing]

end Blotto.PlayerSpecificNestedSpecProfileExecution
