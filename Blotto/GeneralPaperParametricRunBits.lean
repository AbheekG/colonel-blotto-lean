import Blotto.GeneralPaperParametricPriceProfiles

/-! Complete bit-priced native field recursion, including one initial table
and every executed parametric stage. The native affine/height/containment
invariants discharge all callback prices on actual returned prefixes.
-/
namespace Blotto.GeneralPaperParametricRunBits
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayAffineDPSize GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (S h : ℕ) (beta : ℚ) (fields : List (Field K)) (lo hi : ℚ) :
    Option (GeneralPaperRayParametricDP.Output S K) × ℕ :=
  GeneralPaperParametricRecursionPrice.run W
    (fun _ => GeneralPaperParametricInitialPrice.run (fun w => w) W S K)
    (fun field previous lower upper => GeneralPaperParametricStageBits.run model W matrix x w h beta field previous lower upper)
    fields lo hi

theorem data {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (S h : ℕ) (beta : ℚ) (fields : List (Field K)) (lo hi : ℚ) :
    (run model W matrix x w S h beta fields lo hi).1=GeneralPaperRayParametricDP.run
      (GeneralPaperRayPricedPredicate.query matrix x w S h beta) S fields lo hi := by
  apply GeneralPaperParametricRecursionPrice.data
  · exact GeneralPaperParametricInitialPrice.data _ _ _ _
  · exact fun field previous lower upper => GeneralPaperParametricStageBits.data model W matrix x w h beta field previous lower upper

theorem work {m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ)
    (hD : 0<D) (hE : 0<E) (hED : E∣D)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a))
    (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a)) (S h : ℕ) (beta : ℚ)
    (hb : GeneralPaperRayRationalBound.Bounded D P beta) (fields : List (Field K))
    (hLen : fields.length≤m) (hf : ∀ f∈fields,FieldBounded D E X V f)
    (lo hi : ℚ) (hLo : 0≤lo) (hOrder : lo≤hi) (hHi : hi≤1)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P))
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) (hBatch : binaryWordWidth ((S+1)*(K*K)+3)≤W) :
    (run model W matrix x w S h beta fields lo hi).2≤
      GeneralPaperParametricPriceProfiles.profile fields.length m S K W (model.rat (6*width D E m X V P+9)) := by
  let query := GeneralPaperRayPricedPredicate.query matrix x w S h beta
  let initial := fun (_ : Unit) => GeneralPaperParametricInitialPrice.run (fun w => w) W S K
  let stage : GeneralPaperParametricRecursionPrice.Stage S K := fun field previous lower upper => GeneralPaperParametricStageBits.run model W matrix x w h beta field previous lower upper
  let C := GeneralPaperParametricStageBits.profile ((S+1)*(K*K)) m S K W (model.rat (6*width D E m X V P+9))
  have hInitial : (initial ()).1=GeneralPaperRayAffineScoreInput.initial S K := GeneralPaperParametricInitialPrice.data _ _ _ _
  have hStage : ∀ field previous lower upper,(stage field previous lower upper).1=
      GeneralPaperRayParametricStage.stage query field previous lower upper :=
    fun field previous lower upper => GeneralPaperParametricStageBits.data model W matrix x w h beta field previous lower upper
  have hStageCost : ∀ field rest,(field::rest).Sublist fields → ∀ previous,
      GeneralPaperRayParametricDP.run query S rest lo hi=some previous →
        (stage field previous.table previous.bracket.lower previous.bracket.upper).2≤C := by
    intro field rest hSub previous hRun
    have hRestSub : rest.Sublist fields := (List.Sublist.cons field (List.Sublist.refl rest)).trans hSub
    have hRest : ∀ f∈rest,FieldBounded D E X V f := fun f hf' => hf f (hRestSub.subset hf')
    have hProcessed : rest.length+1≤m := by
      have hs := hSub.length_le.trans hLen
      simpa only [List.length_cons] using hs
    have hHeight := GeneralPaperRayParametricRunSize.bracket hD hE query rest lo hi (by omega) hRest hl hh previous hRun
    have hInside := GeneralPaperRayBracketContainment.run query rest lo hi hOrder previous hRun
    have hTable := GeneralPaperRayAffineDPSize.run D E X V S query rest lo hi hRest previous hRun
    have hCost := GeneralPaperParametricStageBits.work model W D E X V P rest.length hD hE hED hProcessed
      matrix x w hx hw h beta hb field previous.table (hf field (hSub.subset List.mem_cons_self)) hTable
      previous.bracket.lower previous.bracket.upper (hLo.trans hInside.1) hInside.2.1 (hInside.2.2.trans hHi)
      hHeight.1 hHeight.2 hW hK hM hIndex hBatch
    exact hCost.trans (GeneralPaperParametricPriceProfiles.stage_batch_mono
      (GeneralPaperRayAffineScoreStep.crossings_length field previous.table) m S K W _)
  exact GeneralPaperParametricRecursionPrice.work query W (120*(S+1)*W) C initial stage hInitial hStage fields lo hi
    (GeneralPaperParametricInitialPrice.bit_work W S K hW hIndex) hStageCost fields (List.Sublist.refl fields)

end Blotto.GeneralPaperParametricRunBits
