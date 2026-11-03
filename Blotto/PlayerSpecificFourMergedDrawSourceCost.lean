import Blotto.PlayerSpecificFourMergedDrawExecution

/-! All actual work in the small uniform component is charged from the
original four-input height and the requested finite-bit precisions. -/
namespace Blotto.PlayerSpecificFourMergedDrawSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicFourInput PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (T H K : ℕ) : ℕ :=
  PlayerSpecificFourMergedInputSourceCost.work T+
  PlayerSpecificThreeDrawSourceCost.coefficient*(iterate 15 T+H+K+1)^16+
  PlayerSpecificSplitFirstTwoSourceCost.work (iterate 3 (iterate 35 T+2*K+6))+2

theorem cost (root : Candidate) (a : Input) (T H K : ℕ) (bits : Fin (8*H+K) → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hT : 2≤T) (ha : Fits root a T) :
    (PlayerSpecificFourMergedDrawExecution.run RationalCostModel.schoolbook root a H K bits).2≤work T H K := by
  let model:=RationalCostModel.schoolbook
  let p:=PlayerSpecificFourMergedInputExecution.run model root a
  let y:=PlayerSpecificThreeDrawExecution.run model root p.1.child H K bits
  let U:=iterate 3 (iterate 35 T+2*K+6)
  have h15 : T ≤ iterate 15 T := PlayerSpecificAlgebraicExpressionBudget.initial_le 15 T
  have hU : iterate 15 T ≤ U := by
    dsimp only [U]
    exact (PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (by omega : 15≤35)).trans
      ((show iterate 35 T ≤ iterate 35 T+2*K+6 by omega).trans
        (PlayerSpecificAlgebraicExpressionBudget.initial_le 3 _))
  have hp : (Reduced root.polynomial p.1.first ∧ HasHeight p.1.first (iterate 15 T)) ∧
      (Reduced root.polynomial p.1.second ∧ HasHeight p.1.second (iterate 15 T)) ∧
      PlayerSpecificAlgebraicThreeEnvironmentSizes.Fits root p.1.child (iterate 15 T) := by
    dsimp only [p]
    rw [PlayerSpecificFourMergedInputExecution.value]
    exact PlayerSpecificAlgebraicFourMergedSizes.bounds model root a T ha hm hm0 hml hmT hT
  have hh : ∀ j,HasHeight (y.1.read j) U := by
    dsimp only [y]
    rw [PlayerSpecificThreeDrawExecution.value]
    have h:=PlayerSpecificAlgebraicThreeDraw.heights model root p.1.child H K bits hm hm0 hml (iterate 15 T)
      (mono hmT h15) (hT.trans h15) hp.2.2
    change ∀ j,HasHeight ((PlayerSpecificAlgebraicThreeDraw.draw model root p.1.child H K bits).read j)
      (iterate 3 (iterate 20 (iterate 15 T)+2*K+6)) at h
    rw [PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add] at h
    exact h
  have hr : ∀ j,Reduced root.polynomial (y.1.read j) := by
    dsimp only [y]
    rw [PlayerSpecificThreeDrawExecution.value]
    exact PlayerSpecificAlgebraicThreeDraw.reduced model root p.1.child H K bits hm hm0
  have hi:=PlayerSpecificFourMergedInputSourceCost.cost root a T hm hm0 hml hmT he hv hT ha
  have hc:=PlayerSpecificThreeDrawSourceCost.cost root p.1.child (iterate 15 T) H K bits hm hm0 hml
    (mono hmT h15) (mono he h15) hv (hT.trans h15) hp.2.2
  have hs:=PlayerSpecificSplitFirstTwoSourceCost.cost root p.1.first p.1.second y.1 U hm hm0 hml
    (mono hmT (h15.trans hU)) (mono he (h15.trans hU)) hv
    ((show 1≤T by omega).trans (h15.trans hU))
    ⟨hp.1.1,mono hp.1.2 hU⟩ ⟨hp.2.1.1,mono hp.2.1.2 hU⟩
    (fun j => ⟨hr j,hh j⟩)
  have hpack : price model [.control 1]=2 := rfl
  change p.2+y.2+(PlayerSpecificSplitFirstTwoExecution.run model root p.1.first p.1.second y.1).2+
    price model [.control 1]≤_
  rw [hpack]
  unfold work
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hi hc) hs) 2

theorem same_return_and_cost (root : Candidate) (a : Input) (T H K : ℕ)
    (bits : Fin (8*H+K) → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hT : 2≤T) (ha : Fits root a T) :
    (PlayerSpecificFourMergedDrawExecution.run RationalCostModel.schoolbook root a H K bits).1=
      PlayerSpecificAlgebraicFourMergedDraw.draw RationalCostModel.schoolbook root a H K bits ∧
    (PlayerSpecificFourMergedDrawExecution.run RationalCostModel.schoolbook root a H K bits).2≤work T H K :=
  ⟨PlayerSpecificFourMergedDrawExecution.value _ root a H K bits,
    cost root a T H K bits hm hm0 hml hmT he hv hT ha⟩

end Blotto.PlayerSpecificFourMergedDrawSourceCost
