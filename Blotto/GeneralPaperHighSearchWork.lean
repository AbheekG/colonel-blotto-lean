import Blotto.GeneralPaperHighSearchBits

/-! Complete native high-endpoint search in the unit arithmetic model.
Input materialization, full recursion, final budget refinement and original
row recovery are all included without operand-width or bit-index premises.
-/
namespace Blotto.GeneralPaperHighSearchWork
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def run {m K : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta lo hi : ℚ) : Option (GeneralPaperRayHighSearch.Answer m K) × ℕ :=
  GeneralPaperHighSearchPriceControl.run 1
    (fun _ => GeneralPaperAffineInputPrice.run (fun _ => 1) 1 matrix x w)
    (GeneralPaperParametricRunWork.run matrix x w S h beta)
    (fun table lower upper => GeneralPaperFinalRefinementPrice.arithmetic matrix table x w h beta lower upper)
    (fun table lower upper => GeneralPaperHighBlockerPrice.run (fun _ => 1) (fun _ => 1) 1 m table h beta lower upper) lo hi

theorem data {m K : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta lo hi : ℚ) :
    (run matrix x w S h beta lo hi).1=GeneralPaperRayHighSearch.prepared matrix S h beta x w lo hi := by
  apply GeneralPaperHighSearchPriceControl.data _ _ _ _ _ matrix x w h beta
  · exact GeneralPaperAffineInputPrice.data _ _ _ _ _
  · exact GeneralPaperParametricRunWork.data matrix x w S h beta
  · exact fun table lower upper => GeneralPaperFinalRefinementPrice.arithmetic_data matrix table x w h beta lower upper
  · exact fun table lower upper => GeneralPaperHighBlockerPrice.data _ _ _ _ table h beta lower upper

theorem actual_data {T m K : ℕ} (scoreDepth : ℕ) (d : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ) (lo hi : ℚ) :
    (run (GeneralPaperScoreMatrixWork.matrixRun scoreDepth d v S).1 x w S h beta lo hi).1=
      GeneralPaperRayHighSearch.search scoreDepth d v S h beta x w lo hi := data _ x w S h beta lo hi

theorem work {m K : ℕ} (D E X V P : ℕ) (hD : 0<D) (hE : 0<E)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a))
    (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a)) (S h : ℕ) (beta : ℚ)
    (hb : GeneralPaperRayRationalBound.Bounded D P beta) (lo hi : ℚ)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P)) :
    (run matrix x w S h beta lo hi).2≤GeneralPaperHighSearchPriceFacts.profile m S K 1 1 := by
  let query := GeneralPaperRayPricedPredicate.query matrix x w S h beta
  let inputs := fun (_ : Unit) => GeneralPaperAffineInputPrice.run (fun _ => 1) 1 matrix x w
  let loop : GeneralPaperHighSearchPriceControl.Loop S K := GeneralPaperParametricRunWork.run matrix x w S h beta
  let finish : GeneralPaperHighSearchPriceControl.Finish S K := fun table lower upper =>
    GeneralPaperFinalRefinementPrice.arithmetic matrix table x w h beta lower upper
  let recover : GeneralPaperHighSearchPriceControl.Recover m S K := fun table lower upper =>
    GeneralPaperHighBlockerPrice.run (fun _ => 1) (fun _ => 1) 1 m table h beta lower upper
  have hInputs : (inputs ()).1=GeneralPaperRayAffineScoreInput.fields matrix x w := GeneralPaperAffineInputPrice.data _ _ _ _ _
  have hLength : (inputs ()).1.length=m := by rw [hInputs,GeneralPaperRayAffineScoreInput.fields_length]
  have hFields : ∀ f∈(inputs ()).1,GeneralPaperRayAffineDPSize.FieldBounded D E X V f := by
    rw [hInputs]
    exact GeneralPaperRayAnchorBound.fields D E X V matrix x w hx hw
  have hLoop := GeneralPaperParametricRunWork.work D E X V P hD hE matrix x w S h beta
    (inputs ()).1 hLength.le hFields lo hi hl hh
  rw [hLength] at hLoop
  have hNative (out) (hr : (loop (inputs ()).1 lo hi).1=some out) :
      GeneralPaperRayParametricDP.run query S (GeneralPaperRayAffineScoreInput.fields matrix x w) lo hi=some out := by
    simpa only [loop,GeneralPaperParametricRunWork.data,hInputs] using hr
  have hFinish : ∀ out,(loop (inputs ()).1 lo hi).1=some out →
      (finish out.table out.bracket.lower out.bracket.upper).2≤GeneralPaperFinalRefinementPrice.profile m S K 1 1 := by
    intro out hr
    have hs := GeneralPaperHighSearchPriceFacts.state D E X V P hD hE matrix x w hx hw h beta lo hi hl hh out (hNative out hr)
    exact GeneralPaperFinalRefinementPrice.arithmetic_work D E X V P m hD hE le_rfl matrix out.table hs.1
      x w h beta hb out.bracket.lower out.bracket.upper hs.2.1 hs.2.2
  have hRecover : ∀ out b,(loop (inputs ()).1 lo hi).1=some out →
      (finish out.table out.bracket.lower out.bracket.upper).1=some b →
        (recover out.table b.lower b.upper).2≤GeneralPaperHighBlockerPrice.profile m S 1 1 := by
    intro out b hr hf
    have hs := GeneralPaperHighSearchPriceFacts.state D E X V P hD hE matrix x w hx hw h beta lo hi hl hh out (hNative out hr)
    have hFinal : GeneralPaperRayFinalBudget.finish matrix out.table x w h beta out.bracket.lower out.bracket.upper=some b := by
      simpa only [finish,GeneralPaperFinalRefinementPrice.arithmetic_data] using hf
    have hBounds := GeneralPaperRayParametricRunSize.finish hD hE (Nat.le_refl m) query out.table hs.1
      h beta out.bracket.lower out.bracket.upper hb hs.2.1 hs.2.2 b hFinal
    exact GeneralPaperHighBlockerPrice.arithmetic_work D E m X V P hD hE out.table hs.1 h beta hb
      b.lower b.upper hBounds.1 hBounds.2.1
  simpa only [run,inputs,loop,finish,recover,GeneralPaperHighSearchPriceFacts.profile,Nat.mul_one] using
    GeneralPaperHighSearchPriceControl.work 1 (512*(m+1)*(K+1))
      (GeneralPaperParametricPriceProfiles.profile m m S K 1 1) (GeneralPaperFinalRefinementPrice.profile m S K 1 1)
      (GeneralPaperHighBlockerPrice.profile m S 1 1) inputs loop finish recover lo hi
      (GeneralPaperAffineInputPrice.arithmetic_work matrix x w) hLoop hFinish hRecover

end Blotto.GeneralPaperHighSearchWork
