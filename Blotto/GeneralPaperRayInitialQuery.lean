import Blotto.GeneralPaperRayQueryWork

/-! Actual entry to the paper's ray search: compute the static scan, then
query its endpoint once. The normalization derives the score cap, while
a next-coordinate velocity of one derives a finite endpoint. A rejected
endpoint supplies a nonempty bracket; an accepted endpoint is maximal for
the full original polytope. The crossing refinement of a rejected bracket
remains a separate algorithmic join.
-/
namespace Blotto.GeneralPaperRayInitialQuery
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperStrictScore
open GeneralPaperStaticRayRows GeneralPaperStaticRayScan GeneralPaperStaticRaySound
open GeneralPaperRayFeasibility GeneralPaperRayBracket
set_option autoImplicit false
set_option maxHeartbeats 2500000

def beginRay {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (v : RationalFieldSelector m)
    (S h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ) :
    Option (GeneralPaperRayMinimum.Choice (StaticIndex T m K) × Bool) :=
  let result := scan labels x w
  match result.choice with
  | none => none
  | some c => some (c,test v S h beta x w c.time)

theorem begin_at_scan {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (v : RationalFieldSelector m)
    (S h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ) (c : GeneralPaperRayMinimum.Choice (StaticIndex T m K))
    (hc : (scan labels x w).choice=some c) :
    beginRay labels v S h beta x w=some (c,test v S h beta x w c.time) := by
  simp only [beginRay,hc]

theorem available {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (v : RationalFieldSelector m)
    (S h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ)
    (hStart : GeneralPaperAffineConstraintRows.Feasible labels (score v S) h (beta:ℝ) (fun j => (x j:ℝ)))
    (next : Variable m K) (hVelocity : w next=1) :
    ∃ c,beginRay labels v S h beta x w=some (c,test v S h beta x w c.time) ∧
      (scan labels x w).choice=some c ∧ 0≤c.time ∧ c.time≤1 ∧
      0<(evaluate labels x w c.blocker).1.slope ∧ (evaluate labels x w c.blocker).1.value c.time=0 := by
  obtain ⟨c,hc,hn,hCap,hp,hTight⟩ := finite_endpoint labels (score v S) h (beta:ℝ) x w hStart next hVelocity
  exact ⟨c,begin_at_scan labels v S h beta x w c hc,hc,hn,hCap,hp,hTight⟩

theorem actual_scores {T m K : ℕ} (depth : ℕ) (d : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) (hCap : S<2^depth) :
    GeneralPaperRayQueryWork.scores (GeneralPaperScoreMatrixWork.matrixRun depth d v S).1=score v S := by
  funext j l
  simp only [GeneralPaperRayQueryWork.scores,GeneralPaperScoreMatrixWork.matrix_data depth d v S hK hCap,
    FixedArrayTable.read_ofFn]

theorem actual_priced_minimum {T m K : ℕ} (depth : ℕ) (d : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) (hCap : S<2^depth)
    (x w : Variable m K → ℚ) (t : ℚ) (h : ℕ) :
    (GeneralPaperRayQueryWork.minimumRun (GeneralPaperScoreMatrixWork.matrixRun depth d v S).1 x w t S h).1=
      GeneralPaperRayHighMinimum.minimum (score v S) (GeneralPaperRayAnchorCosts.costs x w t) S h := by
  rw [GeneralPaperRayQueryWork.minimum_data,actual_scores depth d v S hK hCap]

end Blotto.GeneralPaperRayInitialQuery
