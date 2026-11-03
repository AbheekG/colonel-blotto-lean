import Blotto.GeneralPaperHighSearchPriceControl

/-! Reuse the actual native state invariants when composing all high-search
phases. They hold for returned prefixes without a supplied state/size oracle.
-/
namespace Blotto.GeneralPaperHighSearchPriceFacts
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayUniformSize GeneralPaperRayAffineDPSize
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem state {m S K : ℕ} (D E X V P : ℕ) (hD : 0<D) (hE : 0<E)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a))
    (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a)) (h : ℕ) (beta lo hi : ℚ)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P))
    (out : GeneralPaperRayParametricDP.Output S K)
    (hr : GeneralPaperRayParametricDP.run (GeneralPaperRayPricedPredicate.query matrix x w S h beta) S
      (GeneralPaperRayAffineScoreInput.fields matrix x w) lo hi=some out) :
    TableBounded D E X V m out.table ∧ RationalHeight out.bracket.lower (width D E m X V P) ∧
      RationalHeight out.bracket.upper (width D E m X V P) := by
  have hf := GeneralPaperRayAnchorBound.fields D E X V matrix x w hx hw
  have ht := GeneralPaperRayAffineDPSize.run D E X V S _ _ lo hi hf out hr
  rw [GeneralPaperRayAffineScoreInput.fields_length] at ht
  have hLength : (GeneralPaperRayAffineScoreInput.fields matrix x w).length≤m := by rw [GeneralPaperRayAffineScoreInput.fields_length]
  have hs := GeneralPaperRayParametricRunSize.bracket hD hE _ _ lo hi hLength hf hl hh out hr
  exact ⟨ht,hs.1,hs.2⟩

def profile (m S K W P : ℕ) : ℕ :=
  GeneralPaperHighSearchPriceControl.profile (512*(m+1)*(K+1)*W)
    (GeneralPaperParametricPriceProfiles.profile m m S K W P)
    (GeneralPaperFinalRefinementPrice.profile m S K W P) (GeneralPaperHighBlockerPrice.profile m S W P) W

end Blotto.GeneralPaperHighSearchPriceFacts
