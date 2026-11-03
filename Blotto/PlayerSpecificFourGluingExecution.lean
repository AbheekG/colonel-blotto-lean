import Blotto.PlayerSpecificFourParentInputSourceCost

/-! Complete four-variable gluing computes the eight parameters once,
retains both input records and three-variable parents once, then builds
the measured cached overlap table. -/
namespace Blotto.PlayerSpecificFourGluingExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicFourInput PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) : Descriptor 4 81×ℕ :=
  let p:=PlayerSpecificFourParameterExecution.run model root a
  let firstInput:=PlayerSpecificFourParentInputExecution.run model root a p.1 false
  let first:=PlayerSpecificUnorderedThreeExecution.run model root firstInput.1
  let secondInput:=PlayerSpecificFourParentInputExecution.run model root a p.1 true
  let second:=PlayerSpecificUnorderedThreeExecution.run model root secondInput.1
  let result:=PlayerSpecificOverlapTableExecution.run model root first.1 second.1 (p.1.read 1) a.budget
  (result.1,p.2+firstInput.2+first.2+secondInput.2+second.2+result.2+price model (List.replicate 4 (.control 1)))

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).1=PlayerSpecificAlgebraicFourGluingTable.prepare model root a := by
  simp only [run,PlayerSpecificFourParameterExecution.value,PlayerSpecificFourParentInputExecution.value,
    Bool.false_eq_true,ite_false,ite_true,PlayerSpecificUnorderedThreeExecution.value,
    PlayerSpecificOverlapTableExecution.value,PlayerSpecificAlgebraicFourGluingTable.prepare]
theorem packing (model : RationalCostModel) : price model (List.replicate 4 (.control 1))=8 := rfl

theorem price_equation (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).2=(PlayerSpecificFourParameterExecution.run model root a).2+
      (PlayerSpecificFourParentInputExecution.run model root a (parameters model root a) false).2+
      (PlayerSpecificUnorderedThreeExecution.run model root (PlayerSpecificAlgebraicFourGluingInputs.first root a (parameters model root a))).2+
      (PlayerSpecificFourParentInputExecution.run model root a (parameters model root a) true).2+
      (PlayerSpecificUnorderedThreeExecution.run model root (PlayerSpecificAlgebraicFourGluingInputs.second a (parameters model root a))).2+
      (PlayerSpecificOverlapTableExecution.run model root
        (PlayerSpecificAlgebraicUnorderedThree.prepare model root (PlayerSpecificAlgebraicFourGluingInputs.first root a (parameters model root a)))
        (PlayerSpecificAlgebraicUnorderedThree.prepare model root (PlayerSpecificAlgebraicFourGluingInputs.second a (parameters model root a)))
        ((parameters model root a).read 1) a.budget).2+8 := by
  simp only [run,PlayerSpecificFourParameterExecution.value,PlayerSpecificFourParentInputExecution.value,
    Bool.false_eq_true,ite_false,ite_true,PlayerSpecificUnorderedThreeExecution.value,packing]

end Blotto.PlayerSpecificFourGluingExecution
