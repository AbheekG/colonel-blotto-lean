import Blotto.GeneralPaperRayTableFeasibility

/-! The final budget batch narrows with the same actual full-score query.
Its remaining open interval is infeasible: otherwise fixed signs would
make the whole open interval feasible, and closed-endpoint affine algebra
would contradict the retained infeasible right endpoint.
-/
namespace Blotto.GeneralPaperRayFinalBudget
open RationalOrderCell GeneralPaperStrictScore GeneralPaperRayAffineScoreStep GeneralPaperRayAnchorCosts
open GeneralPaperRayFeasibility GeneralPaperRayTableFeasibility GeneralPaperRayBudgetCrossings
open GeneralPaperRayCrossingRefinement GeneralPaperRayPricedPredicate
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem open_infeasible {m S K : ℕ} (v : RationalFieldSelector m) (hK : 0<K) (x w : Variable m K → ℚ)
    (table : Table S K) (h : ℕ) (beta lo hi : ℚ) (hOrder : lo<hi)
    (hUpper : test v S h beta x w hi=false)
    (hBest : ∀ t,lo<t ∧ t<hi → ∀ s,GeneralPaperMinimum.Best (GeneralPaperExactScoreDP.Fits
      (GeneralPaperExactScoreDP.fields (score v S) (costs x w t)) s.val) ((tableAt table t).read s))
    (hNoCross : ∀ r∈batch table h beta,¬(lo<r ∧ r<hi)) :
    ∀ t,lo<t ∧ t<hi → test v S h beta x w t=false := by
  intro t ht
  cases he : test v S h beta x w t with
  | false => rfl
  | true =>
    have hTable := (test_iff v hK x w table h beta t (hBest t ht)).mp he
    have hAll (u : ℚ) (hu : lo<u ∧ u<hi) : GeneralPaperRayHighSound.HighFeasible (score v S) (costs x w u) h beta := by
      apply (GeneralPaperRayTableFeasibility.high_iff (score v S) x w table h beta u
        (fun labels => GeneralPaperComputedThreshold.totalScore_le v S hK labels) (hBest u hu)).mp
      exact (table_stable table h beta lo hi t u ht hu hNoCross).mp hTable
    have hRight := (GeneralPaperRayTupleResidual.high_closed (score v S) x w h beta lo hi hOrder hAll).2
    have hTrue := (GeneralPaperRayHighSound.passes_iff (score v S) (costs x w hi) S h
      (fun labels => GeneralPaperComputedThreshold.totalScore_le v S hK labels) beta).mpr hRight
    change test v S h beta x w hi=true at hTrue
    rw [hUpper] at hTrue
    contradiction

def finish {m S K : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (table : Table S K)
    (x w : Variable m K → ℚ) (h : ℕ) (beta lo hi : ℚ) : Option Bracket :=
  narrow (query matrix x w S h beta) lo hi (batch table h beta)

theorem actual_sound {T m S K : ℕ} (scoreDepth : ℕ) (d : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (hK : 0<K) (hCap : S<2^scoreDepth) (x w : Variable m K → ℚ)
    (table : Table S K) (h : ℕ) (beta lo hi : ℚ) (hLo : 0≤lo) (hOrder : lo<hi)
    (hStart : test v S h beta x w 0=true) (hLower : test v S h beta x w lo=true) (hUpper : test v S h beta x w hi=false)
    (hBest : ∀ t,lo<t ∧ t<hi → ∀ s,GeneralPaperMinimum.Best (GeneralPaperExactScoreDP.Fits
      (GeneralPaperExactScoreDP.fields (score v S) (costs x w t)) s.val) ((tableAt table t).read s)) :
    ∃ b,finish (GeneralPaperScoreMatrixWork.matrixRun scoreDepth d v S).1 table x w h beta lo hi=some b ∧
      lo≤b.lower ∧ b.lower<b.upper ∧ b.upper≤hi ∧
        test v S h beta x w b.lower=true ∧ test v S h beta x w b.upper=false ∧
          (∀ r∈batch table h beta,¬(b.lower<r ∧ r<b.upper)) ∧
            ∀ t,b.lower<t ∧ t<b.upper → test v S h beta x w t=false := by
  obtain ⟨b,hRun,hL,hOrder',hU,hTrue,hFalse,hNoCross⟩ := GeneralPaperRayActualRefinement.actual_narrow
    scoreDepth d v hK S h hCap beta x w hStart lo hi hLo hOrder (batch table h beta) hLower hUpper
  refine ⟨b,hRun,hL,hOrder',hU,hTrue,hFalse,hNoCross,?_⟩
  apply open_infeasible v hK x w table h beta b.lower b.upper hOrder' hFalse
  · intro t ht
    exact hBest t ⟨hL.trans_lt ht.1,ht.2.trans_le hU⟩
  · exact hNoCross

end Blotto.GeneralPaperRayFinalBudget
