import Blotto.GeneralPaperParametricRunBits

/-! Complete native parametric field recursion with unit rational and index
prices. The initial table is built once, every reached stage is executed
once, and failure/return control is included without operand-width factors.
-/
namespace Blotto.GeneralPaperParametricRunWork
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayAffineDPSize GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {m K : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (S h : ℕ) (beta : ℚ) (fields : List (Field K)) (lo hi : ℚ) :
    Option (GeneralPaperRayParametricDP.Output S K) × ℕ :=
  GeneralPaperParametricRecursionPrice.run 1
    (fun _ => GeneralPaperParametricInitialPrice.run (fun _ => 1) 1 S K)
    (fun field previous lower upper => GeneralPaperParametricStageWork.run matrix x w h beta field previous lower upper)
    fields lo hi

theorem data {m K : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (S h : ℕ) (beta : ℚ) (fields : List (Field K)) (lo hi : ℚ) :
    (run matrix x w S h beta fields lo hi).1=GeneralPaperRayParametricDP.run
      (GeneralPaperRayPricedPredicate.query matrix x w S h beta) S fields lo hi := by
  apply GeneralPaperParametricRecursionPrice.data
  · exact GeneralPaperParametricInitialPrice.data _ _ _ _
  · exact fun field previous lower upper => GeneralPaperParametricStageWork.data matrix x w h beta field previous lower upper

theorem work {m K : ℕ} (D E X V P : ℕ) (hD : 0<D) (hE : 0<E)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (S h : ℕ) (beta : ℚ) (fields : List (Field K)) (hLen : fields.length≤m)
    (hf : ∀ f∈fields,FieldBounded D E X V f) (lo hi : ℚ)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P)) :
    (run matrix x w S h beta fields lo hi).2≤GeneralPaperParametricPriceProfiles.profile fields.length m S K 1 1 := by
  let query := GeneralPaperRayPricedPredicate.query matrix x w S h beta
  let initial := fun (_ : Unit) => GeneralPaperParametricInitialPrice.run (fun _ => 1) 1 S K
  let stage : GeneralPaperParametricRecursionPrice.Stage S K := fun field previous lower upper =>
    GeneralPaperParametricStageWork.run matrix x w h beta field previous lower upper
  let C := GeneralPaperParametricStageBits.profile ((S+1)*(K*K)) m S K 1 1
  have hInitial : (initial ()).1=GeneralPaperRayAffineScoreInput.initial S K := GeneralPaperParametricInitialPrice.data _ _ _ _
  have hStage : ∀ field previous lower upper,(stage field previous lower upper).1=
      GeneralPaperRayParametricStage.stage query field previous lower upper :=
    fun field previous lower upper => GeneralPaperParametricStageWork.data matrix x w h beta field previous lower upper
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
    have hTable := GeneralPaperRayAffineDPSize.run D E X V S query rest lo hi hRest previous hRun
    have hCost := GeneralPaperParametricStageWork.work D E X V P rest.length hD hE hProcessed matrix x w h beta
      field previous.table (hf field (hSub.subset List.mem_cons_self)) hTable previous.bracket.lower previous.bracket.upper
      hHeight.1 hHeight.2
    exact hCost.trans (GeneralPaperParametricPriceProfiles.stage_batch_mono
      (GeneralPaperRayAffineScoreStep.crossings_length field previous.table) m S K 1 1)
  simpa only [run,initial,stage,GeneralPaperParametricPriceProfiles.profile,C,Nat.mul_one] using
    GeneralPaperParametricRecursionPrice.work query 1 (120*(S+1)) C initial stage hInitial hStage fields lo hi
      (GeneralPaperParametricInitialPrice.arithmetic_work S K) hStageCost fields (List.Sublist.refl fields)

end Blotto.GeneralPaperParametricRunWork
