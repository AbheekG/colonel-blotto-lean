import Blotto.PlayerSpecificSplitFirstTwoSourceCost

/-! Scaled/merged input construction retains one parameter table,
three scaled lengths, their first sum and literal probability once. -/
namespace Blotto.PlayerSpecificFourMergedInputExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicFourMergedInput (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def fields (p : Prepared) : FixedArrayTable 7 Data := FixedArrayTable.ofFn
  ![p.first,p.second,p.child.budget,p.child.first,p.child.second,p.child.third,p.child.probability]
def packing : Trace := .control 5::List.replicate 10 (.control 1)
def run (model : RationalCostModel) (root : Candidate) (a : Input) : Prepared×ℕ :=
  let p:=PlayerSpecificFourParameterExecution.run model root a
  let scale:=p.1.read 5
  let first:=PlayerSpecificMixtureScalarExecution.scale model root scale a.first
  let second:=PlayerSpecificMixtureScalarExecution.scale model root scale a.second
  let third:=PlayerSpecificMixtureScalarExecution.scale model root scale a.third
  let merged:=PlayerSpecificFieldCombination.run false root.polynomial first.1 second.1
  let one:=PlayerSpecificFieldCombinationContract.constant root.polynomial 1
  let result:Prepared:=⟨first.1,second.1,⟨a.budget,merged.1,third.1,a.length,one.1⟩⟩
  (result,p.2+first.2+second.2+third.2+price model merged.2+price model one.2+
    price model (PlayerSpecificExpressionVectorExecution.frame root (environment a) (fields result))+price model packing)

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).1=PlayerSpecificAlgebraicFourMergedInput.prepare model root a := by
  simp only [run,PlayerSpecificFourParameterExecution.value,PlayerSpecificMixtureScalarExecution.scale_value,
    PlayerSpecificFieldCombination.value,Bool.false_eq_true,ite_false,PlayerSpecificFieldCombinationContract.constant_value,
    PlayerSpecificAlgebraicFourMergedInput.prepare]
theorem packing_cost (model : RationalCostModel) : price model packing=24 := rfl

theorem price_equation (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).2=(PlayerSpecificFourParameterExecution.run model root a).2+
      (PlayerSpecificMixtureScalarExecution.scale model root ((parameters model root a).read 5) a.first).2+
      (PlayerSpecificMixtureScalarExecution.scale model root ((parameters model root a).read 5) a.second).2+
      (PlayerSpecificMixtureScalarExecution.scale model root ((parameters model root a).read 5) a.third).2+
      price model (PlayerSpecificFieldCombination.run false root.polynomial
        (PlayerSpecificAlgebraicField.times root.polynomial ((parameters model root a).read 5) a.first)
        (PlayerSpecificAlgebraicField.times root.polynomial ((parameters model root a).read 5) a.second)).2+
      price model (PlayerSpecificFieldCombinationContract.constant root.polynomial 1).2+
      price model (PlayerSpecificExpressionVectorExecution.frame root (environment a) (fields (run model root a).1))+24 := by
  simp only [run,PlayerSpecificFourParameterExecution.value,PlayerSpecificMixtureScalarExecution.scale_value,packing_cost]

end Blotto.PlayerSpecificFourMergedInputExecution
