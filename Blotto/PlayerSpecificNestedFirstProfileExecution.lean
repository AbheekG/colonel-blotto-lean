import Blotto.PlayerSpecificNestedSecondUniformSourceCost

/-! The first interior profile retains its outer location and selected
conditional table once, then materializes the feasible padding. -/
namespace Blotto.PlayerSpecificNestedFirstProfileExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) : Descriptor 3 18×ℕ :=
  let location:=PlayerSpecificNestedLocationExecution.run model root a K outer
  let table:=PlayerSpecificNestedFirstTableExecution.run model root a location.1
  let padded:=PlayerSpecificDescriptorPadExecution.run model root table.1 9 0
  (padded.1,location.2+table.2+padded.2+price model [.control 1])

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) :
    (run model root a K outer).1=PlayerSpecificAlgebraicNestedFirstProfile.prepare model root a K outer := by
  simp only [run,PlayerSpecificNestedLocationExecution.value,PlayerSpecificNestedFirstTableExecution.value,
    PlayerSpecificDescriptorPadExecution.value,PlayerSpecificAlgebraicNestedFirstProfile.prepare]
theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl

theorem price_equation (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) :
    (run model root a K outer).2=(PlayerSpecificNestedLocationExecution.run model root a K outer).2+
      (PlayerSpecificNestedFirstTableExecution.run model root a (PlayerSpecificAlgebraicNestedFirstDraw.location model root a K outer)).2+
      (PlayerSpecificDescriptorPadExecution.run model root
        (PlayerSpecificAlgebraicNestedFirstTable.prepare model root a (PlayerSpecificAlgebraicNestedFirstDraw.location model root a K outer)) 9 0).2+2 := by
  simp only [run,PlayerSpecificNestedLocationExecution.value,PlayerSpecificNestedFirstTableExecution.value,packing]

end Blotto.PlayerSpecificNestedFirstProfileExecution
