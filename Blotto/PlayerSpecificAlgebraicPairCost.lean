import Blotto.PlayerSpecificAlgebraicPairSourceCost

/-! The cached pair source price has a polynomial bound in its actual
input coefficient height. All intermediate envelopes are derived here,
including conditional residuals and the divided branch probability. -/
namespace Blotto.PlayerSpecificAlgebraicPairCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 2500000

def height (H : ℕ) : ℕ := PlayerSpecificAlgebraicPairHeights.probabilityHeight H

theorem rows_heights (root : Candidate) (lengthA lengthB a b : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hA : Reduced root.polynomial lengthA) (hB : Reduced root.polynomial lengthB)
    (ha : Reduced root.polynomial a) (hb : Reduced root.polynomial b)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hAH : HasHeight lengthA H) (hBH : HasHeight lengthB H) (haH : HasHeight a H) (hbH : HasHeight b H) :
    ∀ row∈PlayerSpecificAlgebraicPairSourceCost.rows root lengthA lengthB a b,HasHeight row (height H) := by
  let model:=RationalCostModel.schoolbook
  let r:=PlayerSpecificAlgebraicPairStep.run model root lengthA lengthB a b
  let G:=PlayerSpecificAlgebraicPairHeights.resourceHeight H
  let Q:=height H
  have hG : H≤G := by dsimp [G,PlayerSpecificAlgebraicPairHeights.resourceHeight]; omega
  have hQ : 2*G+2≤Q := PlayerSpecificAlgebraicHeightEnvelope.large (2*G+1)
  have hHQ : H≤Q := by omega
  have hs:=PlayerSpecificAlgebraicPairHeights.resources model root lengthA lengthB a b hm hm0 hA hB ha hb H hAH hBH haH hbH
  have hr:=PlayerSpecificAlgebraicPairStep.reduced model root lengthA lengthB a b hm hm0 hA hB
  have hlower : HasHeight r.lowerA G := hs.2.2.2.1
  have hupper : HasHeight r.upperA G := hs.2.1
  have hn:=PlayerSpecificShortReduction.minus_height root.polynomial a r.lowerA hm hm0 ha hr.2.2.2.1
    G G (mono haH hG) hlower
  have hd:=PlayerSpecificShortReduction.minus_height root.polynomial r.upperA r.lowerA hm hm0 hr.2.1 hr.2.2.2.1
    G G hupper hlower
  have hp:=PlayerSpecificAlgebraicPairHeights.probability model root lengthA lengthB a b hm hm0 hml hA hB ha hb H hmH hAH hBH haH hbH
  change ∀ row∈[root.polynomial,[root.interval.lo,root.interval.hi],lengthA,lengthB,a,b,
    r.total,r.upperA,r.upperB,r.lowerA,r.lowerB,PlayerSpecificAlgebraicField.minus root.polynomial a r.lowerA,
      PlayerSpecificAlgebraicField.minus root.polynomial r.upperA r.lowerA,r.probability],HasHeight row Q
  intro row hrow
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hrow
  rcases hrow with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact mono hmH hHQ
  · exact mono he hHQ
  · exact mono hAH hHQ
  · exact mono hBH hHQ
  · exact mono haH hHQ
  · exact mono hbH hHQ
  · exact mono hs.1 (by omega)
  · exact mono hupper (by omega)
  · exact mono hs.2.2.1 (by omega)
  · exact mono hlower (by omega)
  · exact mono hs.2.2.2.2 (by omega)
  · exact mono hn (by omega)
  · exact mono hd (by omega)
  · exact hp

theorem cost (root : Candidate) (lengthA lengthB a b : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hA : Reduced root.polynomial lengthA) (hB : Reduced root.polynomial lengthB)
    (ha : Reduced root.polynomial a) (hb : Reduced root.polynomial b)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi)
    (hAH : HasHeight lengthA H) (hBH : HasHeight lengthB H) (haH : HasHeight a H) (hbH : HasHeight b H) :
    (PlayerSpecificAlgebraicPairExecution.run RationalCostModel.schoolbook root lengthA lengthB a b).2≤
      (2*PlayerSpecificAlgebraicComparisonExecution.coefficient+10000000000)*(height H+1)*
        RationalCostModel.schoolbook.rat (PlayerSpecificAlgebraicComparisonExecution.width (height H)) := by
  have hh:=rows_heights root lengthA lengthB a b H hm hm0 hml hA hB ha hb hmH he hAH hBH haH hbH
  have hQ : 1≤height H := by
    have h:=PlayerSpecificAlgebraicHeightEnvelope.large (2*PlayerSpecificAlgebraicPairHeights.resourceHeight H+1)
    change 1≤PlayerSpecificAlgebraicHeightEnvelope.step (2*PlayerSpecificAlgebraicPairHeights.resourceHeight H+1)
    omega
  exact PlayerSpecificAlgebraicPairSourceCost.cost root lengthA lengthB a b (height H) hm hm0 hml hA hB ha hb hv hh hQ

theorem cubic_profile (C D s : ℕ) (hs : 1≤s) :
    C*s*((D*s)*(D*s)+D*s)≤C*(D*D+D)*s^3 := by
  have h:=Nat.mul_le_mul_left (C*s) (PlayerSpecificAlgebraicInverseContract.quadratic_profile 1 D s hs)
  simpa only [Nat.one_mul] using h.trans_eq (by ring)

theorem height_linear (H : ℕ) :
    height H+1≤(8*PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)*(H+1) := by
  have h:=PlayerSpecificAlgebraicPairHeights.probability_linear H
  change PlayerSpecificAlgebraicPairHeights.probabilityHeight H+1≤_
  nlinarith only [h,Nat.zero_le H]

def polynomialCoefficient : ℕ :=
  (2*PlayerSpecificAlgebraicComparisonExecution.coefficient+10000000000)*
    ((2*PlayerSpecificAlgebraicInitialPrimitiveCost.widthCoefficient)^2+2*PlayerSpecificAlgebraicInitialPrimitiveCost.widthCoefficient)*
      (8*PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3

theorem polynomial_cost (root : Candidate) (lengthA lengthB a b : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hA : Reduced root.polynomial lengthA) (hB : Reduced root.polynomial lengthB)
    (ha : Reduced root.polynomial a) (hb : Reduced root.polynomial b)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi)
    (hAH : HasHeight lengthA H) (hBH : HasHeight lengthB H) (haH : HasHeight a H) (hbH : HasHeight b H) :
    (PlayerSpecificAlgebraicPairExecution.run RationalCostModel.schoolbook root lengthA lengthB a b).2≤
      polynomialCoefficient*(H+1)^3 := by
  let C:=2*PlayerSpecificAlgebraicComparisonExecution.coefficient+10000000000
  let D:=2*PlayerSpecificAlgebraicInitialPrimitiveCost.widthCoefficient
  let E:=8*PlayerSpecificAlgebraicHeightEnvelope.coefficient+1
  have hc:=cost root lengthA lengthB a b H hm hm0 hml hA hB ha hb hmH he hv hAH hBH haH hbH
  have hw : PlayerSpecificAlgebraicComparisonExecution.width (height H)=D*(height H+1) := by
    dsimp [PlayerSpecificAlgebraicComparisonExecution.width,PlayerSpecificAlgebraicInitialPrimitiveCost.width,D]
    ring
  rw [hw] at hc
  change _≤C*(height H+1)*((D*(height H+1))*(D*(height H+1))+D*(height H+1)) at hc
  have hp:=cubic_profile C D (height H+1) (by omega)
  have ht : (height H+1)^3≤(E*(H+1))^3 := Nat.pow_le_pow_left (height_linear H) 3
  calc
    _ ≤ C*(D*D+D)*(height H+1)^3 := hc.trans hp
    _ ≤ C*(D*D+D)*(E*(H+1))^3 := Nat.mul_le_mul_left _ ht
    _ = polynomialCoefficient*(H+1)^3 := by change _=C*(D^2+D)*E^3*(H+1)^3; ring

end Blotto.PlayerSpecificAlgebraicPairCost
