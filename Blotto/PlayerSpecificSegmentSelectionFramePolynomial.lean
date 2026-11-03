import Blotto.PlayerSpecificSegmentSelectionSizes

/-! Actual segment selection caller frames have polynomial source
prices at a size derived from masses, weights and coin precision. -/
namespace Blotto.PlayerSpecificSegmentSelectionFramePolynomial
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicReduction PlayerSpecificSegmentSelectionSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cost {slots : ℕ} (root : Candidate) (weights : FixedArrayTable slots Data) (fallback : Fin slots)
    (H : ℕ) (items : List (Fin slots)) (remaining probability next : Data) (blocks : ℕ) (result : Fin slots×ℕ)
    (S : ℕ) (hm : HasHeight root.polynomial S) (hml : root.polynomial.length≤4)
    (he : HasHeight [root.interval.lo,root.interval.hi] S)
    (hw : ∀ j,Reduced root.polynomial (weights.read j) ∧ HasHeight (weights.read j) S)
    (hr : Reduced root.polynomial remaining ∧ HasHeight remaining S)
    (hp : Reduced root.polynomial probability ∧ HasHeight probability (PlayerSpecificAlgebraicHeightEnvelope.step S))
    (hn : Reduced root.polynomial next ∧ HasHeight next S)
    (hi : items.length≤slots) (hb : blocks≤slots) (hv : result.2≤slots) :
    price RationalCostModel.schoolbook (PlayerSpecificSegmentSelectionExecution.frame root weights fallback H items remaining probability next blocks result)≤
      ((1000*(slots+1))*PlayerSpecificResourceCostProfile.rationalCoefficient)*(size S H slots+1)^3 := by
  let U:=size S H slots
  have hlow:=lower S H slots
  have hc:=PlayerSpecificSegmentSelectionFrameCost.cost RationalCostModel.schoolbook root weights fallback H items remaining probability next blocks result U
    (mono hm hlow.1) hml (mono he hlow.1) (mono hr.2 hlow.1) (by have h:=hr.1.2; omega)
    (mono hp.2 hlow.2.1) (by have h:=hp.1.2; omega) (mono hn.2 hlow.1) (by have h:=hn.1.2; omega)
    (fun j => ⟨mono (hw j).2 hlow.1,by have h:=(hw j).1.2; omega⟩) hi hlow.2.2.2.1 hlow.2.2.1
    (hb.trans hlow.2.2.2.1) (hv.trans hlow.2.2.2.1) hlow.2.2.2.2
  exact hc.trans (rational_polynomial (1000*(slots+1)) U)

end Blotto.PlayerSpecificSegmentSelectionFramePolynomial
