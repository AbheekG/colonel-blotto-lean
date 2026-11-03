import Blotto.PlayerSpecificNestedLocationSourceCost

/-! The conditional profile retains one family, one reached location
and one selected conditional table, including the enclosing return. -/
namespace Blotto.PlayerSpecificNestedProfileExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) (short : Data) (K : ℕ) (outer : Fin K → Bool) : Descriptor 3 9×ℕ :=
  let family:=PlayerSpecificNestedFamilyExecution.run model root a short
  let location:=PlayerSpecificNestedLocationExecution.run model root family.1 K outer
  let table:=PlayerSpecificNestedFirstTableExecution.run model root family.1 location.1
  (table.1,family.2+location.2+table.2+price model [.control 1])

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (short : Data) (K : ℕ) (outer : Fin K → Bool) :
    (run model root a short K outer).1=PlayerSpecificAlgebraicNestedFamily.profile model root a short K outer := by
  simp only [run,PlayerSpecificNestedFamilyExecution.value,PlayerSpecificNestedLocationExecution.value,
    PlayerSpecificNestedFirstTableExecution.value,PlayerSpecificAlgebraicNestedFamily.profile]
theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl

theorem price_equation (model : RationalCostModel) (root : Candidate) (a : Input) (short : Data) (K : ℕ) (outer : Fin K → Bool) :
    (run model root a short K outer).2=(PlayerSpecificNestedFamilyExecution.run model root a short).2+
      (PlayerSpecificNestedLocationExecution.run model root (PlayerSpecificAlgebraicNestedFamily.family model root a short) K outer).2+
      (PlayerSpecificNestedFirstTableExecution.run model root (PlayerSpecificAlgebraicNestedFamily.family model root a short)
        (PlayerSpecificAlgebraicNestedFirstDraw.location model root (PlayerSpecificAlgebraicNestedFamily.family model root a short) K outer)).2+2 := by
  simp only [run,PlayerSpecificNestedFamilyExecution.value,PlayerSpecificNestedLocationExecution.value,packing]

end Blotto.PlayerSpecificNestedProfileExecution
