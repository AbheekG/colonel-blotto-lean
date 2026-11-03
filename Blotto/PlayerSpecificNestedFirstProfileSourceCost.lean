import Blotto.PlayerSpecificNestedFirstProfileExecution

/-! Complete eighteen-slot first profile source work, with midpoint,
conditional table and padding heights derived from original raw rows. -/
namespace Blotto.PlayerSpecificNestedFirstProfileSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def locationHeight (H K : ℕ) : ℕ := iterate 10 (PlayerSpecificAlgebraicNestedFirstDrawSizes.base H K)
def tableHeight (H K : ℕ) : ℕ := iterate 32 (PlayerSpecificAlgebraicNestedFirstDrawSizes.base H K)
def work (H K : ℕ) : ℕ := PlayerSpecificNestedLocationSourceCost.work H K+
  PlayerSpecificNestedFirstTableSourceCost.work (locationHeight H K)+
  PlayerSpecificDescriptorPadSourceCost.work (tableHeight H K) 3 9 9+2

theorem cost (root : Candidate) (a : Input) (H K : ℕ) (outer : Fin K → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H) :
    (PlayerSpecificNestedFirstProfileExecution.run RationalCostModel.schoolbook root a K outer).2≤work H K := by
  let model:=RationalCostModel.schoolbook
  let location:=PlayerSpecificAlgebraicNestedFirstDraw.location model root a K outer
  let table:=PlayerSpecificAlgebraicNestedFirstTable.prepare model root a location
  let T:=locationHeight H K
  let U:=tableHeight H K
  have hHT : H≤T := by
    have hi:=PlayerSpecificAlgebraicExpressionBudget.initial_le 10 (H+K+3)
    change H ≤ iterate 10 (H+K+3)
    omega
  have hHU : H≤U := by
    have hi:=PlayerSpecificAlgebraicExpressionBudget.initial_le 32 (H+K+3)
    change H ≤ iterate 32 (H+K+3)
    omega
  have hlb:=PlayerSpecificAlgebraicNestedFirstDrawSizes.location_bounds model root a H ha hm hm0 hml hmH hH K outer
  have htb:=PlayerSpecificAlgebraicNestedFirstDrawSizes.table_bounds model root a H ha hm hm0 hml hmH hH K outer
  have hl:=PlayerSpecificNestedLocationSourceCost.cost root a H K outer hm hm0 hml hmH he hv hH ha
  have ht:=PlayerSpecificNestedFirstTableSourceCost.cost root a location T hm hm0 hml (mono hmH hHT) (mono he hHT) hv
    (hH.trans hHT) (PlayerSpecificAlgebraicNestedInputTools.fits_mono root a H T ha hHT) hlb
  have hp:=PlayerSpecificDescriptorPadSourceCost.cost root table 9 0 U hm0 hml (mono hmH hHU) (mono he hHU) htb
  rw [PlayerSpecificNestedFirstProfileExecution.price_equation]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hl ht) hp) 2

end Blotto.PlayerSpecificNestedFirstProfileSourceCost
