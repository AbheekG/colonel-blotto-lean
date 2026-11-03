import Blotto.GeneralPaperFinalStaticCheckSound

/-! The final checker runs one original static scan and one complete
score DP on a stored rational point. The score matrix is supplied by the
shared preparation; no whole tuple is enumerated or supplied as an oracle.
-/
namespace Blotto.GeneralPaperFinalPolytopeCheck
open RationalOrderCell GeneralPaperExactScoreDP
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Result where
  accepted : Bool
  work : ℕ

def run {T m K : ℕ} (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (Field K))
    (S h : ℕ) (beta : ℚ) (x : Variable m K → ℚ) : Result :=
  let static := GeneralPaperFinalStaticCheck.run labels x
  let high := GeneralPaperRayPricedPredicate.query matrix x (fun _ => 0) S h beta 0
  ⟨static.accepted && high.1,static.work+high.2+8⟩

theorem correct {T m K : ℕ} (depth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h : ℕ) (hK : 0<K) (hCap : S<2^depth) (beta : ℚ) (x : Variable m K → ℚ) :
    (run dict.label (GeneralPaperScoreMatrixWork.matrixRun depth dict v S).1 S h beta x).accepted=true ↔
      GeneralPaperAffineConstraintRows.Feasible dict.label (GeneralPaperStrictScore.score v S) h (beta:ℝ) (fun a => (x a:ℝ)) := by
  have hh := GeneralPaperRayFeasibility.full_iff dict.label v hK S h beta x (fun _ => 0) 0
  simp only [GeneralPaperStaticRaySound.StaticFeasible,Rat.cast_zero,zero_mul,add_zero] at hh
  change ((GeneralPaperFinalStaticCheck.run dict.label x).accepted &&
    (GeneralPaperRayPricedPredicate.query (GeneralPaperScoreMatrixWork.matrixRun depth dict v S).1 x (fun _ => 0) S h beta 0).1)=true ↔ _
  rw [Bool.and_eq_true,GeneralPaperFinalStaticCheckSound.correct dict.label x (beta:ℝ),
    GeneralPaperRayPricedPredicate.actual_data depth dict v S hK hCap x (fun _ => 0) h beta 0]
  exact hh.symm

theorem work {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (Field K))
    (S h : ℕ) (beta : ℚ) (x : Variable m K → ℚ) :
    (run labels matrix S h beta x).work≤512*(m*(K-1)+m*T+m+1)+1024*(m+1)*(K+1)*(S+1)+16 := by
  have hs := GeneralPaperFinalStaticCheckSound.work hm labels x
  have hh := GeneralPaperRayPricedPredicate.query_work matrix x (fun _ => 0) S h beta 0
  change (GeneralPaperFinalStaticCheck.run labels x).work+
    (GeneralPaperRayPricedPredicate.query matrix x (fun _ => 0) S h beta 0).2+8≤_
  omega

end Blotto.GeneralPaperFinalPolytopeCheck
