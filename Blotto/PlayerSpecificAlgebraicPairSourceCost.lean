import Blotto.PlayerSpecificAlgebraicPairExecution

/-! Source-cost composition for the actual cached pair at a common
operand envelope. The following original-height theorem derives this
envelope from the previously checked disjoint-lineage pair bounds. -/
namespace Blotto.PlayerSpecificAlgebraicPairSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 2500000

def rows (root : Candidate) (lengthA lengthB a b : Data) : List Data :=
  let r:=PlayerSpecificAlgebraicPairStep.run RationalCostModel.schoolbook root lengthA lengthB a b
  [root.polynomial,[root.interval.lo,root.interval.hi],lengthA,lengthB,a,b,r.total,r.upperA,r.upperB,r.lowerA,r.lowerB,
    PlayerSpecificAlgebraicField.minus root.polynomial a r.lowerA,
    PlayerSpecificAlgebraicField.minus root.polynomial r.upperA r.lowerA,r.probability]

theorem profile (A R H : ℕ) :
    2*(A*(H+1)*R)+10000000000*R≤(2*A+10000000000)*(H+1)*R := by
  nlinarith only [Nat.zero_le (H*R)]

theorem cost (root : Candidate) (lengthA lengthB a b : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hA : Reduced root.polynomial lengthA) (hB : Reduced root.polynomial lengthB)
    (ha : Reduced root.polynomial a) (hb : Reduced root.polynomial b)
    (hv : root.interval.lo<root.interval.hi)
    (hh : ∀ row∈rows root lengthA lengthB a b,HasHeight row H) (hH : 1≤H) :
    (PlayerSpecificAlgebraicPairExecution.run RationalCostModel.schoolbook root lengthA lengthB a b).2≤
      (2*PlayerSpecificAlgebraicComparisonExecution.coefficient+10000000000)*(H+1)*
        RationalCostModel.schoolbook.rat (PlayerSpecificAlgebraicComparisonExecution.width H) := by
  let model:=RationalCostModel.schoolbook
  let m:=root.polynomial
  let r:=PlayerSpecificAlgebraicPairStep.run model root lengthA lengthB a b
  let numerator:=PlayerSpecificAlgebraicField.minus m a r.lowerA
  let denominator:=PlayerSpecificAlgebraicField.minus m r.upperA r.lowerA
  let W:=PlayerSpecificAlgebraicComparisonExecution.width H
  have hmlm : m.length≤4 := hml
  have hmem : ∀ row∈[m,[root.interval.lo,root.interval.hi],lengthA,lengthB,a,b,r.total,r.upperA,r.upperB,r.lowerA,r.lowerB,
      numerator,denominator,r.probability],HasHeight row H := hh
  have hred:=PlayerSpecificAlgebraicPairStep.reduced model root lengthA lengthB a b hm hm0 hA hB
  have htr : Reduced m r.total := hred.1
  have hur : Reduced m r.upperA := hred.2.1
  have hlr : Reduced m r.lowerA := hred.2.2.2.1
  have hnr : Reduced m numerator := PlayerSpecificAlgebraicField.minus_reduced m a r.lowerA hm hm0
  have hdr : Reduced m denominator := PlayerSpecificAlgebraicField.minus_reduced m r.upperA r.lowerA hm hm0
  have hheight : ∀ row∈[m,[root.interval.lo,root.interval.hi],lengthA,lengthB,a,b,r.total,r.upperA,r.upperB,r.lowerA,r.lowerB,
      numerator,denominator,r.probability],HasHeight row H := hmem
  have hshort : ∀ row∈[m,[root.interval.lo,root.interval.hi],lengthA,lengthB,a,b,r.total,r.upperA,r.upperB,r.lowerA,r.lowerB,
      numerator,denominator,r.probability],row.length≤21 := by
    have hlen : ∀ c,Reduced m c → c.length≤21 := by intro c hc; have hl:=hc.2; omega
    intro row hrow
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hrow
    rcases hrow with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · omega
    · simp
    · exact hlen _ hA
    · exact hlen _ hB
    · exact hlen _ ha
    · exact hlen _ hb
    · exact hlen _ htr
    · exact hlen _ hur
    · exact hlen _ hred.2.2.1
    · exact hlen _ hlr
    · exact hlen _ hred.2.2.2.2.1
    · exact hlen _ hnr
    · exact hlen _ hdr
    · exact hlen _ hred.2.2.2.2.2
  have hlarge:=PlayerSpecificAlgebraicInitialPrimitiveCost.large (2*H+1)
  have hW : 32≤W := by change 32≤PlayerSpecificAlgebraicInitialPrimitiveCost.width (2*H+1); omega
  have hHW : 1+2*H≤W := by change 1+2*H≤PlayerSpecificAlgebraicInitialPrimitiveCost.width (2*H+1); omega
  have hw : PlayerSpecificAlgebraicInitialPrimitiveCost.width H≤W := by
    apply Nat.mul_le_mul_left PlayerSpecificAlgebraicInitialPrimitiveCost.widthCoefficient
    omega
  have hfwidth : PlayerSpecificFieldCombinationCost.width H≤W := by
    exact (Nat.mul_le_mul_right (H+1) (show PlayerSpecificFieldCombinationCost.widthCoefficient≤
      PlayerSpecificAlgebraicInitialPrimitiveCost.widthCoefficient by unfold PlayerSpecificAlgebraicInitialPrimitiveCost.widthCoefficient; omega)).trans hw
  have hc : ∀ (difference : Bool) (u v : Data),Reduced m u → Reduced m v → HasHeight u H → HasHeight v H →
      price model (PlayerSpecificFieldCombination.run difference m u v).2≤200000000*model.rat W := by
    intro difference u v hu hv huH hvH
    exact (PlayerSpecificFieldCombinationCost.run_cost model difference m u v hm hm0 hml H
      (hheight m (by simp)) huH hvH hH (by have hl:=hu.2; omega) (by have hl:=hv.2; omega)).trans
        (Nat.mul_le_mul_left _ (model.monotone hfwidth))
  have htotal:=hc false a b ha hb (hheight a (by simp)) (hheight b (by simp))
  have hupper:=hc true r.total lengthA htr hA (hheight r.total (by simp)) (hheight lengthA (by simp))
  have hlower:=hc true r.total lengthB htr hB (hheight r.total (by simp)) (hheight lengthB (by simp))
  have hnum:=hc true a r.lowerA ha hlr (hheight a (by simp)) (hheight r.lowerA (by simp))
  have hden:=hc true r.upperA r.lowerA hur hlr (hheight r.upperA (by simp)) (hheight r.lowerA (by simp))
  have hdiv:=(PlayerSpecificAlgebraicInitialPrimitiveCost.division_cost model m numerator denominator H hm hm0 hml hnr hdr
    (hheight m (by simp)) (hheight numerator (by simp)) (hheight denominator (by simp)) hH).trans
      (Nat.mul_le_mul_left _ (model.monotone hw))
  have hcmpA:=PlayerSpecificAlgebraicComparisonExecution.cost model root r.total lengthA H hm hm0 hml
    (hheight m (by simp)) (hheight _ (by simp)) hv (hheight r.total (by simp)) (hheight lengthA (by simp))
    (by have hl:=htr.2; omega) (by have hl:=hA.2; omega) hH
  have hcmpB:=PlayerSpecificAlgebraicComparisonExecution.cost model root r.total lengthB H hm hm0 hml
    (hheight m (by simp)) (hheight _ (by simp)) hv (hheight r.total (by simp)) (hheight lengthB (by simp))
    (by have hl:=htr.2; omega) (by have hl:=hB.2; omega) hH
  have hframe:=PlayerSpecificAlgebraicCallerFrame.cost model _ [2,6] H W hheight hshort
    (by intro word hword; simp only [List.mem_cons,List.not_mem_nil,or_false] at hword; rcases hword with rfl|rfl <;> exact (control_width _).trans (by omega)) hHW hW
  have hframe' : price model (PlayerSpecificAlgebraicPairExecution.frame root lengthA lengthB a b numerator denominator r)≤930*model.rat W := by
    simpa only [PlayerSpecificAlgebraicPairExecution.frame,List.length_cons,List.length_nil] using hframe
  apply le_trans ?_ (profile PlayerSpecificAlgebraicComparisonExecution.coefficient (model.rat W) H)
  dsimp only [PlayerSpecificAlgebraicPairExecution.run]
  simp only [PlayerSpecificFieldCombination.value,PlayerSpecificAlgebraicComparisonExecution.value,Bool.false_eq_true,ite_false,ite_true]
  by_cases h1 : PlayerSpecificAlgebraicPairStep.le model root r.total lengthA=true <;>
    by_cases h2 : PlayerSpecificAlgebraicPairStep.le model root r.total lengthB=true
  all_goals
    dsimp only [r,PlayerSpecificAlgebraicPairStep.run,m,numerator,denominator,model,W] at htotal hupper hlower hnum hden hdiv hcmpA hcmpB hframe' h1 h2 ⊢
    simp only [h1,h2,Bool.false_eq_true,ite_true,ite_false,PlayerSpecificFieldCombination.value,PlayerSpecificFieldDivisionExecution.value,
      show price RationalCostModel.schoolbook []=0 from rfl] at htotal hupper hlower hnum hden hdiv hcmpA hcmpB hframe' ⊢
    omega

end Blotto.PlayerSpecificAlgebraicPairSourceCost
