import Blotto.GeneralPaperRayPricedPredicate

/-! Join crossing-bracket refinement to the actual full-score feasibility
test, with fixed normalized scores and stored indexed inputs. The query
count is logarithmic, and every tested point pays a complete priced DP.
-/
namespace Blotto.GeneralPaperRayActualRefinement
open RationalOrderCell GeneralPaperStrictScore GeneralPaperRayFeasibility
open GeneralPaperRayCrossingRefinement GeneralPaperRayPricedPredicate
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem actual_narrow {T m K : ℕ} (scoreDepth : ℕ) (d : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (hK : 0<K) (S h : ℕ) (hCap : S<2^scoreDepth)
    (beta : ℚ) (x w : Variable m K → ℚ) (hStart : test v S h beta x w 0=true)
    (lo hi : ℚ) (hLo : 0≤lo) (hOrder : lo<hi) (points : List ℚ)
    (hLower : test v S h beta x w lo=true) (hUpper : test v S h beta x w hi=false) :
    let matrix := (GeneralPaperScoreMatrixWork.matrixRun scoreDepth d v S).1
    ∃ b,narrow (query matrix x w S h beta) lo hi points=some b ∧
      lo≤b.lower ∧ b.lower<b.upper ∧ b.upper≤hi ∧
        test v S h beta x w b.lower=true ∧ test v S h beta x w b.upper=false ∧
          ∀ t∈points,¬(b.lower<t ∧ t<b.upper) := by
  dsimp only
  let matrix := (GeneralPaperScoreMatrixWork.matrixRun scoreDepth d v S).1
  have hData (t : ℚ) : (query matrix x w S h beta t).1=test v S h beta x w t :=
    actual_data scoreDepth d v S hK hCap x w h beta t
  obtain ⟨b,hRun,hSound⟩ := narrow_sound (query matrix x w S h beta) lo hi hOrder points
    (by rw [hData]; exact hLower) (by rw [hData]; exact hUpper) (by
      intro s t hs hst _ ht
      rw [hData] at ht ⊢
      exact GeneralPaperRayBracket.test_downclosed v hK S h beta x w hStart t ht s ⟨hLo.trans hs,hst⟩)
  exact ⟨b,hRun,hSound.1,hSound.2.1,hSound.2.2.1,
    by rw [←hData]; exact hSound.2.2.2.1,by rw [←hData]; exact hSound.2.2.2.2.1,hSound.2.2.2.2.2⟩

theorem probe_bound {m K n : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (points : FixedArrayTable n ℚ) (x w : Variable m K → ℚ) (S h : ℕ) (beta : ℚ) :
    (GeneralPaperRaySearchControls.selected (fun i => query matrix x w S h beta (points.read i))).probes≤binaryWordWidth n+1 :=
  GeneralPaperRaySearchControls.logarithmic_probes _

theorem search_work {m K n : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (points : FixedArrayTable n ℚ) (x w : Variable m K → ℚ) (S h : ℕ) (beta : ℚ) :
    (GeneralPaperRaySearchControls.selected (fun i => query matrix x w S h beta (points.read i))).work≤
      GeneralPaperRaySearchControls.depth n*(12*GeneralPaperRaySearchControls.depth n+42+1024*(m+1)*(K+1)*(S+1))+
        12*binaryWordWidth n+26 := by
  have hh := GeneralPaperRaySearchControls.selected_work
    (fun i => query matrix x w S h beta (points.read i)) (1024*(m+1)*(K+1)*(S+1)+8)
    (fun i => query_work matrix x w S h beta (points.read i))
  have he : 12*GeneralPaperRaySearchControls.depth n+34+(1024*(m+1)*(K+1)*(S+1)+8)=
      12*GeneralPaperRaySearchControls.depth n+42+1024*(m+1)*(K+1)*(S+1) := by omega
  rwa [he] at hh

end Blotto.GeneralPaperRayActualRefinement
