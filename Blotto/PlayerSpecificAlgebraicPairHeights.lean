import Blotto.PlayerSpecificAlgebraicPairContract

/-! Resource updates use only reduced additions/subtractions. The
lottery probability has a fixed arithmetic depth and is never a resource
input on the next update. -/
namespace Blotto.PlayerSpecificAlgebraicPairHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicPairStep
set_option autoImplicit false
set_option maxHeartbeats 2500000

def resourceHeight (H : ℕ) : ℕ := 3*(H+1)
def probabilityHeight (H : ℕ) : ℕ := PlayerSpecificAlgebraicHeightEnvelope.step (2*resourceHeight H+1)

theorem resources (model : RationalCostModel) (root : Candidate) (lengthA lengthB a b : Data)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hA : Reduced root.polynomial lengthA) (hB : Reduced root.polynomial lengthB)
    (ha : Reduced root.polynomial a) (hb : Reduced root.polynomial b) (H : ℕ)
    (hAH : HasHeight lengthA H) (hBH : HasHeight lengthB H) (haH : HasHeight a H) (hbH : HasHeight b H) :
    let r:=run model root lengthA lengthB a b
    HasHeight r.total (2*H+1) ∧ HasHeight r.upperA (resourceHeight H) ∧ HasHeight r.upperB (resourceHeight H) ∧
      HasHeight r.lowerA (resourceHeight H) ∧ HasHeight r.lowerB (resourceHeight H) := by
  have ht:=PlayerSpecificShortReduction.plus_height root.polynomial a b hm hm0 ha hb H H haH hbH
  have ht' : HasHeight (PlayerSpecificAlgebraicField.plus root.polynomial a b) (2*H+1) := by simpa only [two_mul] using ht
  have htRed:=PlayerSpecificAlgebraicField.plus_reduced root.polynomial a b hm hm0
  have hu:=PlayerSpecificShortReduction.minus_height root.polynomial _ lengthA hm hm0 htRed hA (2*H+1) H ht' hAH
  have hl:=PlayerSpecificShortReduction.minus_height root.polynomial _ lengthB hm hm0 htRed hB (2*H+1) H ht' hBH
  have htG:=mono ht' (show 2*H+1≤resourceHeight H by unfold resourceHeight; omega)
  have hAG:=mono hAH (show H≤resourceHeight H by unfold resourceHeight; omega)
  have hBG:=mono hBH (show H≤resourceHeight H by unfold resourceHeight; omega)
  have huG:=mono hu (show 2*H+1+H+1≤resourceHeight H by unfold resourceHeight; omega)
  have hlG:=mono hl (show 2*H+1+H+1≤resourceHeight H by unfold resourceHeight; omega)
  have hz:=nil_height (resourceHeight H)
  dsimp only [PlayerSpecificAlgebraicPairStep.run]
  split <;> split <;> exact ⟨ht',by assumption,by assumption,by assumption,by assumption⟩

theorem probability (model : RationalCostModel) (root : Candidate) (lengthA lengthB a b : Data)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hA : Reduced root.polynomial lengthA) (hB : Reduced root.polynomial lengthB)
    (ha : Reduced root.polynomial a) (hb : Reduced root.polynomial b) (H : ℕ)
    (hmH : HasHeight root.polynomial H) (hAH : HasHeight lengthA H) (hBH : HasHeight lengthB H)
    (haH : HasHeight a H) (hbH : HasHeight b H) :
    HasHeight (run model root lengthA lengthB a b).probability (probabilityHeight H) := by
  let r:=run model root lengthA lengthB a b
  have hs:=resources model root lengthA lengthB a b hm hm0 hA hB ha hb H hAH hBH haH hbH
  have hr:=reduced model root lengthA lengthB a b hm hm0 hA hB
  have hinput : H≤resourceHeight H := by unfold resourceHeight; omega
  have hn:=PlayerSpecificShortReduction.minus_height root.polynomial a r.lowerA hm hm0 ha hr.2.2.2.1
    (resourceHeight H) (resourceHeight H) (mono haH hinput) hs.2.2.2.1
  have hd:=PlayerSpecificShortReduction.minus_height root.polynomial r.upperA r.lowerA hm hm0 hr.2.1 hr.2.2.2.1
    (resourceHeight H) (resourceHeight H) hs.2.1 hs.2.2.2.1
  have hmT : HasHeight root.polynomial (2*resourceHeight H+1) := mono hmH (by omega)
  have hnT : HasHeight (PlayerSpecificAlgebraicField.minus root.polynomial a r.lowerA) (2*resourceHeight H+1) := by
    simpa only [two_mul] using hn
  have hdT : HasHeight (PlayerSpecificAlgebraicField.minus root.polynomial r.upperA r.lowerA) (2*resourceHeight H+1) := by
    simpa only [two_mul] using hd
  exact PlayerSpecificAlgebraicHeightEnvelope.divide_height root.polynomial _ _ (2*resourceHeight H+1) hm hm0 hml
    (PlayerSpecificAlgebraicField.minus_reduced _ _ _ hm hm0) (PlayerSpecificAlgebraicField.minus_reduced _ _ _ hm hm0)
    hmT hnT hdT (by omega)

theorem probability_linear (H : ℕ) : probabilityHeight H≤8*PlayerSpecificAlgebraicHeightEnvelope.coefficient*(H+1) := by
  unfold probabilityHeight PlayerSpecificAlgebraicHeightEnvelope.step resourceHeight
  nlinarith only [Nat.zero_le H]

end Blotto.PlayerSpecificAlgebraicPairHeights
