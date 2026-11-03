import Blotto.GeneralPaperHighSearchPriceFacts

/-! Complete bit-priced native high-endpoint search. Input arrays, every
parametric field stage, final budget refinement, fixed violation scan and
original-row decoding are executed once, with all phase/control joins.
-/
namespace Blotto.GeneralPaperHighSearchBits
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def run {m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta lo hi : ℚ) : Option (GeneralPaperRayHighSearch.Answer m K) × ℕ :=
  GeneralPaperHighSearchPriceControl.run W
    (fun _ => GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w)
    (GeneralPaperParametricRunBits.run model W matrix x w S h beta)
    (fun table lower upper => GeneralPaperFinalRefinementPrice.bits model W matrix table x w h beta lower upper)
    (fun table lower upper => GeneralPaperHighBlockerPrice.run model.rat (fun w => w) W m table h beta lower upper) lo hi

theorem data {m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta lo hi : ℚ) :
    (run model W matrix x w S h beta lo hi).1=GeneralPaperRayHighSearch.prepared matrix S h beta x w lo hi := by
  apply GeneralPaperHighSearchPriceControl.data _ _ _ _ _ matrix x w h beta
  · exact GeneralPaperAffineInputPrice.data _ _ _ _ _
  · exact GeneralPaperParametricRunBits.data model W matrix x w S h beta
  · exact fun table lower upper => GeneralPaperFinalRefinementPrice.bits_data model W matrix table x w h beta lower upper
  · exact fun table lower upper => GeneralPaperHighBlockerPrice.data _ _ _ _ table h beta lower upper

theorem actual_data {T m K : ℕ} (model : RationalCostModel) (W scoreDepth : ℕ)
    (d : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (S h : ℕ)
    (beta : ℚ) (x w : Variable m K → ℚ) (lo hi : ℚ) :
    (run model W (GeneralPaperScoreMatrixWork.matrixRun scoreDepth d v S).1 x w S h beta lo hi).1=
      GeneralPaperRayHighSearch.search scoreDepth d v S h beta x w lo hi :=
  data model W _ x w S h beta lo hi

theorem work {m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ)
    (hD : 0<D) (hE : 0<E) (hED : E∣D)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a))
    (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a)) (S h : ℕ) (beta : ℚ)
    (hb : GeneralPaperRayRationalBound.Bounded D P beta) (lo hi : ℚ)
    (hLo : 0≤lo) (hOrder : lo≤hi) (hHi : hi≤1)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P))
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) (hBatch : binaryWordWidth ((S+1)*(K*K)+3)≤W)
    (hFinalIndex : binaryWordWidth (S+4)≤W) :
    (run model W matrix x w S h beta lo hi).2≤
      GeneralPaperHighSearchPriceFacts.profile m S K W (model.rat (6*width D E m X V P+9)) := by
  let Q := model.rat (6*width D E m X V P+9)
  let query := GeneralPaperRayPricedPredicate.query matrix x w S h beta
  let inputs := fun (_ : Unit) => GeneralPaperAffineInputPrice.run (fun w => w) W matrix x w
  let loop : GeneralPaperHighSearchPriceControl.Loop S K := GeneralPaperParametricRunBits.run model W matrix x w S h beta
  let finish : GeneralPaperHighSearchPriceControl.Finish S K := fun table lower upper =>
    GeneralPaperFinalRefinementPrice.bits model W matrix table x w h beta lower upper
  let recover : GeneralPaperHighSearchPriceControl.Recover m S K := fun table lower upper =>
    GeneralPaperHighBlockerPrice.run model.rat (fun w => w) W m table h beta lower upper
  have hInputs : (inputs ()).1=GeneralPaperRayAffineScoreInput.fields matrix x w := GeneralPaperAffineInputPrice.data _ _ _ _ _
  have hLength : (inputs ()).1.length=m := by rw [hInputs,GeneralPaperRayAffineScoreInput.fields_length]
  have hFields : ∀ f∈(inputs ()).1,GeneralPaperRayAffineDPSize.FieldBounded D E X V f := by
    rw [hInputs]
    exact GeneralPaperRayAnchorBound.fields D E X V matrix x w hx hw
  have hLoop := GeneralPaperParametricRunBits.work model W D E X V P hD hE hED matrix x w hx hw S h beta hb
    (inputs ()).1 hLength.le hFields lo hi hLo hOrder hHi hl hh hW hK hM hIndex hBatch
  rw [hLength] at hLoop
  have hNative (out) (hr : (loop (inputs ()).1 lo hi).1=some out) :
      GeneralPaperRayParametricDP.run query S (GeneralPaperRayAffineScoreInput.fields matrix x w) lo hi=some out := by
    simpa only [loop,GeneralPaperParametricRunBits.data,hInputs] using hr
  have hFinish : ∀ out,(loop (inputs ()).1 lo hi).1=some out →
      (finish out.table out.bracket.lower out.bracket.upper).2≤GeneralPaperFinalRefinementPrice.profile m S K W Q := by
    intro out hr
    have hn := hNative out hr
    have hs := GeneralPaperHighSearchPriceFacts.state D E X V P hD hE matrix x w hx hw h beta lo hi hl hh out hn
    have hi' := GeneralPaperRayBracketContainment.run query (GeneralPaperRayAffineScoreInput.fields matrix x w) lo hi hOrder out hn
    exact GeneralPaperFinalRefinementPrice.bits_work model W D E X V P m hD hE hED le_rfl matrix out.table hs.1
      x w hx hw h beta hb out.bracket.lower out.bracket.upper (hLo.trans hi'.1) hi'.2.1 (hi'.2.2.trans hHi)
      hs.2.1 hs.2.2 hW hK hM hIndex hFinalIndex
  have hRecover : ∀ out b,(loop (inputs ()).1 lo hi).1=some out →
      (finish out.table out.bracket.lower out.bracket.upper).1=some b →
        (recover out.table b.lower b.upper).2≤GeneralPaperHighBlockerPrice.profile m S W Q := by
    intro out b hr hf
    have hn := hNative out hr
    have hs := GeneralPaperHighSearchPriceFacts.state D E X V P hD hE matrix x w hx hw h beta lo hi hl hh out hn
    have hFinal : GeneralPaperRayFinalBudget.finish matrix out.table x w h beta out.bracket.lower out.bracket.upper=some b := by
      simpa only [finish,GeneralPaperFinalRefinementPrice.bits_data] using hf
    have hBounds := GeneralPaperRayParametricRunSize.finish hD hE (Nat.le_refl m) query out.table hs.1
      h beta out.bracket.lower out.bracket.upper hb hs.2.1 hs.2.2 b hFinal
    exact GeneralPaperHighBlockerPrice.bit_work model W D E m X V P hD hE out.table hs.1 h beta hb
      b.lower b.upper hBounds.1 hBounds.2.1 hW hM
  exact GeneralPaperHighSearchPriceControl.work W (512*(m+1)*(K+1)*W)
    (GeneralPaperParametricPriceProfiles.profile m m S K W Q) (GeneralPaperFinalRefinementPrice.profile m S K W Q)
    (GeneralPaperHighBlockerPrice.profile m S W Q) inputs loop finish recover lo hi
    (GeneralPaperAffineInputPrice.bit_work W matrix x w hW hK hM) hLoop hFinish hRecover

end Blotto.GeneralPaperHighSearchBits
