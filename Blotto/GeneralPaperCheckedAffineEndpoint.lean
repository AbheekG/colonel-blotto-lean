import Blotto.GeneralPaperSharedBasisInputs

/-! Evaluate/check the auxiliary point, then evaluate/check the endpoint,
using one already-built affine cache and one shared score matrix. An
unsuccessful check returns none; no endpoint is evaluated before the
auxiliary check accepts. These are the paper's final polytope rechecks.
-/
namespace Blotto.GeneralPaperCheckedAffineEndpoint
open RationalOrderCell GeneralPaperBasisAffineData GeneralPaperBasisOriginalDirection
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Result (d : ℕ) where
  point : Option (GeneralPaperBasisRationalSolve.RatVector d)
  work : ℕ

def run {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (auxiliary gamma : ℚ)
    (data : Data (m*(K-1))) : Result (m*(K-1)) :=
  let aux := GeneralPaperBasisAffineEvaluate.atRational data auxiliary
  let checkAux := GeneralPaperFinalPolytopeCheck.run labels matrix S h auxiliary (reader aux.1)
  if checkAux.accepted then
    let endpoint := GeneralPaperBasisAffineEvaluate.atRational data gamma
    let checkEnd := GeneralPaperFinalPolytopeCheck.run labels matrix S h gamma (reader endpoint.1)
    ⟨if checkEnd.accepted then some endpoint.1 else none,aux.2+checkAux.work+endpoint.2+checkEnd.work+16⟩
  else ⟨none,aux.2+checkAux.work+8⟩

theorem accepted {T m K : ℕ} (depth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h : ℕ) (hK : 0<K) (hCap : S<2^depth) (auxiliary gamma : ℚ)
    (data : Data (m*(K-1)))
    (hAux : GeneralPaperAffineConstraintRows.Feasible dict.label (GeneralPaperStrictScore.score v S) h (auxiliary:ℝ)
      (fun a => (reader (GeneralPaperBasisAffineEvaluate.atRational data auxiliary).1 a:ℝ)))
    (hEnd : GeneralPaperAffineConstraintRows.Feasible dict.label (GeneralPaperStrictScore.score v S) h (gamma:ℝ)
      (fun a => (reader (GeneralPaperBasisAffineEvaluate.atRational data gamma).1 a:ℝ))) :
    (run dict.label (GeneralPaperScoreMatrixWork.matrixRun depth dict v S).1 S h auxiliary gamma data).point=
      some (GeneralPaperBasisAffineEvaluate.atRational data gamma).1 := by
  have ha := (GeneralPaperFinalPolytopeCheck.correct depth dict v S h hK hCap auxiliary
    (reader (GeneralPaperBasisAffineEvaluate.atRational data auxiliary).1)).mpr hAux
  have he := (GeneralPaperFinalPolytopeCheck.correct depth dict v S h hK hCap gamma
    (reader (GeneralPaperBasisAffineEvaluate.atRational data gamma).1)).mpr hEnd
  simp only [run,ha,he,ite_true]

theorem work {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (auxiliary gamma : ℚ)
    (data : Data (m*(K-1))) :
    (run labels matrix S h auxiliary gamma data).work≤
      192*(m*(K-1)+1)+1024*(m*(K-1)+m*T+m+1)+2048*(m+1)*(K+1)*(S+1)+48 := by
  have ha := GeneralPaperBasisAffineEvaluate.work data auxiliary.num auxiliary.den
  have he := GeneralPaperBasisAffineEvaluate.work data gamma.num gamma.den
  have hca := GeneralPaperFinalPolytopeCheck.work hm labels matrix S h auxiliary
    (reader (GeneralPaperBasisAffineEvaluate.atRational data auxiliary).1)
  have hce := GeneralPaperFinalPolytopeCheck.work hm labels matrix S h gamma
    (reader (GeneralPaperBasisAffineEvaluate.atRational data gamma).1)
  change (GeneralPaperBasisAffineEvaluate.atRational data auxiliary).2≤_ at ha
  change (GeneralPaperBasisAffineEvaluate.atRational data gamma).2≤_ at he
  by_cases hCheck : (GeneralPaperFinalPolytopeCheck.run labels matrix S h auxiliary
      (reader (GeneralPaperBasisAffineEvaluate.atRational data auxiliary).1)).accepted=true
  · simp only [run,hCheck,ite_true]
    nlinarith only [ha,he,hca,hce]
  · simp only [run,hCheck,Bool.false_eq_true,ite_false]
    nlinarith only [ha,hca]

end Blotto.GeneralPaperCheckedAffineEndpoint
