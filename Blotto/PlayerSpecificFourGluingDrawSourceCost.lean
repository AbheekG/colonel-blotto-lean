import Blotto.PlayerSpecificFourGluingDrawExecution

/-! Complete four-variable gluing draw source work is polynomial in
original row height and both precisions, with its table size derived. -/
namespace Blotto.PlayerSpecificFourGluingDrawSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicFourInput PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (T H K : ℕ) : ℕ := PlayerSpecificFourGluingSourceCost.work T+
  PlayerSpecificSegmentDrawSourceCost.coefficient*(iterate 43 T+4+81+H+K+1)^16+2

theorem cost (root : Candidate) (a : Input) (T H K : ℕ) (bits : Fin (80*H+K) → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hT : 2≤T) (ha : Fits root a T) :
    (PlayerSpecificFourGluingDrawExecution.run RationalCostModel.schoolbook root a H K bits).2≤work T H K := by
  let model:=RationalCostModel.schoolbook
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 43 T
  have ht:=PlayerSpecificFourGluingSourceCost.cost root a T hm hm0 hml hmT he hv hT ha
  have hd:=PlayerSpecificAlgebraicFourGluingTable.bounds model root a T ha hm hm0 hml hmT hT
  have hs:=PlayerSpecificSegmentDrawSourceCost.cost root (PlayerSpecificAlgebraicFourGluingTable.prepare model root a) 80 (iterate 43 T) H K bits
    hm hm0 hml (mono hmT hbase) (mono he hbase) hv ((show 1≤T by omega).trans hbase) hd
  rw [PlayerSpecificFourGluingDrawExecution.price_equation]
  exact Nat.add_le_add_right (Nat.add_le_add ht hs) 2

theorem same_return_and_cost (root : Candidate) (a : Input) (T H K : ℕ) (bits : Fin (80*H+K) → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hT : 2≤T) (ha : Fits root a T) :
    (PlayerSpecificFourGluingDrawExecution.run RationalCostModel.schoolbook root a H K bits).1=
      PlayerSpecificAlgebraicFourGluingDraw.draw RationalCostModel.schoolbook root a H K bits ∧
    (PlayerSpecificFourGluingDrawExecution.run RationalCostModel.schoolbook root a H K bits).2≤work T H K :=
  ⟨PlayerSpecificFourGluingDrawExecution.value _ root a H K bits,cost root a T H K bits hm hm0 hml hmT he hv hT ha⟩

end Blotto.PlayerSpecificFourGluingDrawSourceCost
