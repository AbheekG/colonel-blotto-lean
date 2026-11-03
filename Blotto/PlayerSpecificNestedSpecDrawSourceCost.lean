import Blotto.PlayerSpecificNestedSpecDrawExecution

/-! Complete closed-probability nested draw source work from original raw row
height and both bit precisions. No reached table, arithmetic operation,
coefficient height or caller price is supplied as a runtime oracle. -/
namespace Blotto.PlayerSpecificNestedSpecDrawSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (T H K : ℕ) : ℕ :=
  PlayerSpecificNestedPacketSourceCost.coefficient*(PlayerSpecificNestedPacketSourceCost.size 18 H K+1)^3+
  PlayerSpecificNestedSpecProfileSourceCost.work T K+
  PlayerSpecificSegmentDrawSourceCost.coefficient*(PlayerSpecificAlgebraicNestedInteriorSizes.height T K+3+18+H+K+1)^16+2

theorem cost (root : Candidate) (a : Input) (T H K : ℕ) (bits : Fin ((17*H+K)+K) → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hT : 2≤T) (ha : Fits root a T) :
    (PlayerSpecificNestedSpecDrawExecution.run RationalCostModel.schoolbook root a H K bits).2≤work T H K := by
  let model:=RationalCostModel.schoolbook
  let outer:=secondBitBlock (17*H+K) K bits
  let inner:=firstBitBlock (17*H+K) K bits
  let table:=PlayerSpecificAlgebraicNestedSpecProfile.prepare model root a K outer
  let U:=PlayerSpecificAlgebraicNestedInteriorSizes.height T K
  have hTU:=PlayerSpecificAlgebraicNestedInteriorSizes.input_le T K
  have hp:=PlayerSpecificNestedPacketSourceCost.cost 18 H K bits
  have ht:=PlayerSpecificNestedSpecProfileSourceCost.cost root a T K outer hm hm0 hml hmT he hv hT ha
  have hd:=PlayerSpecificAlgebraicNestedSpecSizes.bounds model root a T ha hm hm0 hml hmT hT K outer
  have hs:=PlayerSpecificSegmentDrawSourceCost.cost root table 17 U H K inner hm hm0 hml (mono hmT hTU) (mono he hTU) hv
    ((show 1≤T by omega).trans hTU) hd
  rw [PlayerSpecificNestedSpecDrawExecution.price_equation]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hp ht) hs) 2

theorem same_return_and_cost (root : Candidate) (a : Input) (T H K : ℕ) (bits : Fin ((17*H+K)+K) → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hT : 2≤T) (ha : Fits root a T) :
    (PlayerSpecificNestedSpecDrawExecution.run RationalCostModel.schoolbook root a H K bits).1=
      PlayerSpecificAlgebraicNestedSpecDraw.draw RationalCostModel.schoolbook root a H K bits ∧
    (PlayerSpecificNestedSpecDrawExecution.run RationalCostModel.schoolbook root a H K bits).2≤work T H K :=
  ⟨PlayerSpecificNestedSpecDrawExecution.value _ root a H K bits,cost root a T H K bits hm hm0 hml hmT he hv hT ha⟩

end Blotto.PlayerSpecificNestedSpecDrawSourceCost
