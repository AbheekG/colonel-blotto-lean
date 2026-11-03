import Blotto.PlayerSpecificDescriptorSwapSourceCost

/-! The sorted interior preparation retains its comparison and raw
record once, then restores coordinates only when a swap is required. -/
namespace Blotto.PlayerSpecificNestedSortedProfileExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def input (model : RationalCostModel) (root : Candidate) (a : Input) : (Input×Bool)×ℕ :=
  let tested:=PlayerSpecificAlgebraicComparisonExecution.run model root a.first a.second
  let result:=PlayerSpecificAlgebraicNestedSpecInput.sorted a tested.1
  ((result,tested.1),tested.2+price model (PlayerSpecificExpressionVectorExecution.frame root (environment a []) (environment result []))+
    price model (List.replicate 7 (.control 1)))

def run (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) : Descriptor 3 18×ℕ :=
  let raw:=input model root a
  let profile:=PlayerSpecificNestedInteriorProfileExecution.run model root raw.1.1 K outer
  let restored:=if raw.1.2 then (profile.1,0) else PlayerSpecificDescriptorSwapExecution.run model root profile.1
  (restored.1,raw.2+profile.2+restored.2+price model [.control 1])

theorem input_value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (input model root a).1=(PlayerSpecificAlgebraicNestedSpecInput.sorted a (PlayerSpecificAlgebraicPairStep.le model root a.first a.second),
      PlayerSpecificAlgebraicPairStep.le model root a.first a.second) := by
  simp only [input,PlayerSpecificAlgebraicComparisonExecution.value]
theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (K : ℕ) (outer : Fin K → Bool) :
    (run model root a K outer).1=PlayerSpecificAlgebraicNestedSpecProfile.interior model root a K outer := by
  simp only [run,input_value,PlayerSpecificAlgebraicNestedSpecProfile.interior]
  split <;> simp_all only [PlayerSpecificNestedInteriorProfileExecution.value,PlayerSpecificDescriptorSwapExecution.value]
theorem input_packing (model : RationalCostModel) : price model (List.replicate 7 (.control 1))=14 := rfl
theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl

theorem input_price (model : RationalCostModel) (root : Candidate) (a : Input) :
    (input model root a).2=(PlayerSpecificAlgebraicComparisonExecution.run model root a.first a.second).2+
      price model (PlayerSpecificExpressionVectorExecution.frame root (environment a [])
        (environment (PlayerSpecificAlgebraicNestedSpecInput.sorted a (PlayerSpecificAlgebraicPairStep.le model root a.first a.second)) []))+14 := by
  simp only [input,PlayerSpecificAlgebraicComparisonExecution.value,input_packing]

end Blotto.PlayerSpecificNestedSortedProfileExecution
