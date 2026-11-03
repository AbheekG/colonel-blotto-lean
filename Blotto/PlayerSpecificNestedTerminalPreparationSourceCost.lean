import Blotto.PlayerSpecificNestedTerminalPreparationFrameCost

/-! Complete original-row-height terminal preparation prices its
reached tests, both endpoint choices, one mixture division and record. -/
namespace Blotto.PlayerSpecificNestedTerminalPreparationSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedTerminalInput PlayerSpecificAlgebraicNestedTerminalSizes PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H : ℕ) : ℕ := PlayerSpecificNestedFocusSourceCost.work H+
  PlayerSpecificNestedTerminalEndpointSourceCost.work H+PlayerSpecificNestedTerminalEndpointSourceCost.work H+
  (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(H+1)^3+
  (4200*PlayerSpecificResourceCostProfile.rationalCoefficient)*(step H+21)^3+40

theorem input_bounds (model : RationalCostModel) (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (hH : 1≤H) (ha : Fits root a H) :
    PlayerSpecificAlgebraicNestedParameterSizes.Fits root (PlayerSpecificNestedTerminalPreparationExecution.run model root a).1.input (step H) := by
  rw [PlayerSpecificNestedTerminalPreparationExecution.input_value]
  exact bounds model root a H ha hm hm0 hml hmH hH

theorem cost (root : Candidate) (a : Input) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 1≤H) (ha : Fits root a H) :
    (PlayerSpecificNestedTerminalPreparationExecution.run RationalCostModel.schoolbook root a).2≤work H := by
  let model:=RationalCostModel.schoolbook
  let f:=PlayerSpecificAlgebraicNestedTerminalInput.focus model root a
  let permutation:=Equiv.swap f 2
  have hf:=PlayerSpecificNestedFocusSourceCost.cost root a H hm hm0 hml hmH he hv hH ha
  have hfirst:=PlayerSpecificNestedTerminalEndpointSourceCost.cost root a (permutation 0) H hm hm0 hml hmH he hH ha
  have hsecond:=PlayerSpecificNestedTerminalEndpointSourceCost.cost root a (permutation 1) H hm hm0 hml hmH he hH ha
  have hdivision:=(PlayerSpecificAlgebraicExpressionPrimitiveCost.binary_cost model root .divide (a.resource.read f) (a.capacity.read f) H
    hm hm0 hml (ha.resource f).1 (ha.capacity f).1 hmH (ha.resource f).2 (ha.capacity f).2 hH).trans
      (PlayerSpecificSegmentSelectionSizes.rational_polynomial 8000000000 H)
  have hframe:=PlayerSpecificNestedTerminalPreparationFrameCost.cost root a H hm hm0 hml hmH he hH ha
  have hpacking:=PlayerSpecificNestedTerminalPreparationExecution.packing_cost model f
  rw [PlayerSpecificNestedTerminalPreparationExecution.price_equation]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hf hfirst) hsecond) hdivision) hframe) hpacking

end Blotto.PlayerSpecificNestedTerminalPreparationSourceCost
