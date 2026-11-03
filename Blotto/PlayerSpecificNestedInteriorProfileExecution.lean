import Blotto.PlayerSpecificNestedSecondProfileSourceCost

/-! The complete interior dispatcher computes its case record once,
tests only reached boundaries and executes exactly one case profile. -/
namespace Blotto.PlayerSpecificNestedInteriorProfileExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicNestedCaseParameters (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def selected (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (K : ℕ) (outer : Fin K → Bool) : Descriptor 3 18×ℕ :=
  let first:=PlayerSpecificAlgebraicComparisonExecution.run model root a.short p.v
  if first.1 then
    let result:=PlayerSpecificNestedFirstProfileExecution.run model root a K outer
    (result.1,first.2+result.2+price model [.control 1])
  else
    let second:=PlayerSpecificAlgebraicComparisonExecution.run model root p.u a.short
    let result:=if second.1 then PlayerSpecificNestedSecondProfileExecution.run model root a p K outer
      else PlayerSpecificNestedThirdProfileExecution.run model root a p K outer
    (result.1,first.2+second.2+result.2+price model [.control 1,.control 1])

def run (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) : Descriptor 3 18×ℕ :=
  let parameters:=PlayerSpecificNestedCaseParameterExecution.run model root a
  let result:=selected model root a parameters.1 K outer
  (result.1,parameters.2+result.2+price model [.control 1])

theorem selected_value (model : RationalCostModel) (root : Candidate) (a : Input) (p : Prepared) (K : ℕ) (outer : Fin K → Bool) :
    (selected model root a p K outer).1=PlayerSpecificAlgebraicNestedInteriorProfile.selected model root a p K outer := by
  simp only [selected,PlayerSpecificAlgebraicComparisonExecution.value,PlayerSpecificAlgebraicNestedInteriorProfile.selected]
  split
  · simp only [PlayerSpecificNestedFirstProfileExecution.value]
  · split <;> simp_all only [PlayerSpecificNestedSecondProfileExecution.value,PlayerSpecificNestedThirdProfileExecution.value]
theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) :
    (run model root a K outer).1=PlayerSpecificAlgebraicNestedInteriorProfile.prepare model root a K outer := by
  simp only [run,PlayerSpecificNestedCaseParameterExecution.value,selected_value,PlayerSpecificAlgebraicNestedInteriorProfile.prepare]
theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl
theorem two_tests_packing (model : RationalCostModel) : price model [.control 1,.control 1]=4 := rfl
theorem price_equation (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) :
    (run model root a K outer).2=(PlayerSpecificNestedCaseParameterExecution.run model root a).2+
      (selected model root a (PlayerSpecificAlgebraicNestedCaseParameters.prepare model root a) K outer).2+2 := by
  simp only [run,PlayerSpecificNestedCaseParameterExecution.value,packing]

end Blotto.PlayerSpecificNestedInteriorProfileExecution
