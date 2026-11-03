import Blotto.GeneralPaperRayParametricDP

/-! The actual reused normalized-score matrix and rational ray anchors
feed the complete parametric DP, with the actual priced full-score query
at every binary-search probe. No supplied candidate, minimum or feasible
predicate oracle occurs in this execution.
-/
namespace Blotto.GeneralPaperRayActualParametricDP
open RationalOrderCell GeneralPaperStrictScore GeneralPaperRayFeasibility
open GeneralPaperRayAffineScoreStep GeneralPaperRayPricedPredicate GeneralPaperRayParametricDP
set_option autoImplicit false
set_option maxHeartbeats 3500000

def execute {T m K : ℕ} (scoreDepth : ℕ) (d : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ) (lo hi : ℚ) : Option (Output S K) :=
  let matrix := (GeneralPaperScoreMatrixWork.matrixRun scoreDepth d v S).1
  run (query matrix x w S h beta) S (GeneralPaperRayAffineScoreInput.fields matrix x w) lo hi

theorem actual_sound {T m K : ℕ} (scoreDepth : ℕ) (d : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (hK : 0<K) (S h : ℕ) (hCap : S<2^scoreDepth)
    (beta : ℚ) (x w : Variable m K → ℚ) (hStart : test v S h beta x w 0=true)
    (lo hi : ℚ) (hLo : 0≤lo) (hOrder : lo<hi)
    (hLower : test v S h beta x w lo=true) (hUpper : test v S h beta x w hi=false) :
    ∃ out,execute scoreDepth d v S h beta x w lo hi=some out ∧
      lo≤out.bracket.lower ∧ out.bracket.lower<out.bracket.upper ∧ out.bracket.upper≤hi ∧
        test v S h beta x w out.bracket.lower=true ∧ test v S h beta x w out.bracket.upper=false ∧
          ∀ t,out.bracket.lower<t ∧ t<out.bracket.upper → ∀ s,
            GeneralPaperMinimum.Best (GeneralPaperExactScoreDP.Fits
              (GeneralPaperExactScoreDP.fields (score v S) (GeneralPaperRayAnchorCosts.costs x w t)) s.val)
                ((tableAt out.table t).read s) := by
  let matrix := (GeneralPaperScoreMatrixWork.matrixRun scoreDepth d v S).1
  have hData (t : ℚ) : (query matrix x w S h beta t).1=test v S h beta x w t :=
    actual_data scoreDepth d v S hK hCap x w h beta t
  obtain ⟨out,hRun,hSound⟩ := run_sound (query matrix x w S h beta) S
    (GeneralPaperRayAffineScoreInput.fields matrix x w) lo hi hOrder
    (by rw [hData]; exact hLower) (by rw [hData]; exact hUpper) (by
      intro s t hs hst _ ht
      rw [hData] at ht ⊢
      exact GeneralPaperRayBracket.test_downclosed v hK S h beta x w hStart t ht s ⟨hLo.trans hs,hst⟩)
  refine ⟨out,hRun,hSound.1,hSound.2.1,hSound.2.2.1,
    by rw [←hData]; exact hSound.2.2.2.1,by rw [←hData]; exact hSound.2.2.2.2.1,?_⟩
  intro t ht s
  have hh := hSound.2.2.2.2.2 t ht s
  rw [GeneralPaperRayAffineScoreInput.fields_data] at hh
  have hs : GeneralPaperRayQueryWork.scores matrix=score v S := GeneralPaperRayInitialQuery.actual_scores scoreDepth d v S hK hCap
  rwa [hs] at hh

end Blotto.GeneralPaperRayActualParametricDP
