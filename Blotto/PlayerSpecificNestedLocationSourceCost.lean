import Blotto.PlayerSpecificNestedLocationExecution

/-! Complete actual outer-location source work is polynomial in raw
input height and outer midpoint precision, including zero precision. -/
namespace Blotto.PlayerSpecificNestedLocationSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H K : ℕ) : ℕ := (2000*(192*192+192))*(K+1)^3+
  (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(H+K+4)^3+
  PlayerSpecificNestedParameterSourceCost.scalarCoefficient*(step (H+K+3)+19)^3+2

theorem cost (root : Candidate) (a : Input) (H K : ℕ) (outer : Fin K → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificNestedLocationExecution.run RationalCostModel.schoolbook root a K outer).2≤work H K := by
  let model:=RationalCostModel.schoolbook
  let G:=H+K+3
  let q:=dyadicMidpointSample K outer
  let scalar:=PlayerSpecificAlgebraicField.constant root.polynomial q
  have hHG : H≤G := by dsimp [G]; omega
  have hGS : G≤step G := (Nat.le_succ _).trans (large G)
  have hHS:=hHG.trans hGS
  have hq : RationalHeight q G := (dyadicMidpointSample_height K outer).mono (by dsimp [G]; omega)
  have hscalar : Reduced root.polynomial scalar ∧ HasHeight scalar (step G) :=
    ⟨PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0,
      constant_height root.polynomial q G (mono hmH hHG) hq (by dsimp [G]; omega) hml⟩
  have hmpt:=PlayerSpecificMidpointCost.polynomial_cost K outer
  have hc:=(PlayerSpecificAlgebraicExpressionPrimitiveCost.constant_cost model root q G hm hm0 hml (mono hmH hHG) hq
    (by dsimp [G]; omega)).trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 8000000000 G)
  have hs:=PlayerSpecificNestedParameterSourceCost.scalar_cost root a scalar 0 (step G) hm hm0 hml
    (mono hmH hHS) (mono he hHS) hv (hH.trans hHS)
    (PlayerSpecificAlgebraicNestedInputTools.fits_mono root a H (step G) ha hHS) hscalar
  rw [show G+1=H+K+4 by rfl] at hc
  rw [PlayerSpecificNestedLocationExecution.price_equation]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hmpt hc) hs) 2

end Blotto.PlayerSpecificNestedLocationSourceCost
