import Blotto.GeneralPaperRawAffineEvaluate

/-! Retained raw fractions feed the auxiliary and endpoint evaluations.
The two original-polytope checks share the same score matrix. Only the
auxiliary point is evaluated until its check succeeds. The work bound is
arithmetic only; bit prices of the two final checks remain separate. -/
namespace Blotto.GeneralPaperRawAffineEndpoint
open GeneralPaperBasisAffineData GeneralPaperBasisOriginalDirection
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run {T m K : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ)
    (data : Data (m*(K-1))) : GeneralPaperCheckedAffineEndpoint.Result (m*(K-1)) :=
  let A := if bits then W else 1
  let aux := GeneralPaperRawAffineEvaluate.run bits model W data auxNum auxDen
  let checkAux := GeneralPaperFinalPolytopeCheck.run labels matrix S h auxiliary (reader aux.1)
  if checkAux.accepted then
    let endpoint := GeneralPaperRawAffineEvaluate.run bits model W data endNum endDen
    let checkEnd := GeneralPaperFinalPolytopeCheck.run labels matrix S h gamma (reader endpoint.1)
    ⟨if checkEnd.accepted then some endpoint.1 else none,aux.2+checkAux.work+endpoint.2+checkEnd.work+16*A⟩
  else ⟨none,aux.2+checkAux.work+8*A⟩

theorem point {T m K : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ)
    (hAuxDen : 0<auxDen) (hEndDen : 0<endDen)
    (hAux : (auxNum:ℚ)/(auxDen:ℚ)=auxiliary) (hEnd : (endNum:ℚ)/(endDen:ℚ)=gamma)
    (data : Data (m*(K-1))) :
    (run bits model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen data).point=
      (GeneralPaperCheckedAffineEndpoint.run labels matrix S h auxiliary gamma data).point := by
  simp only [run,GeneralPaperCheckedAffineEndpoint.run,
    GeneralPaperRawAffineEvaluate.represented bits model W data auxNum auxDen hAuxDen auxiliary hAux,
    GeneralPaperRawAffineEvaluate.represented bits model W data endNum endDen hEndDen gamma hEnd]
  split <;> rfl

theorem arithmetic_work {T m K : ℕ} (model : RationalCostModel) (hm : 0<m)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ)
    (data : Data (m*(K-1))) :
    (run false model 1 labels matrix S h auxiliary gamma auxNum endNum auxDen endDen data).work≤
      256*(m*(K-1)+1)+1024*(m*(K-1)+m*T+m+1)+2048*(m+1)*(K+1)*(S+1)+48 := by
  have ha := GeneralPaperRawAffineEvaluate.arithmetic_work model data auxNum auxDen
  have he := GeneralPaperRawAffineEvaluate.arithmetic_work model data endNum endDen
  have hca := GeneralPaperFinalPolytopeCheck.work hm labels matrix S h auxiliary
    (reader (GeneralPaperRawAffineEvaluate.run false model 1 data auxNum auxDen).1)
  have hce := GeneralPaperFinalPolytopeCheck.work hm labels matrix S h gamma
    (reader (GeneralPaperRawAffineEvaluate.run false model 1 data endNum endDen).1)
  by_cases hc : (GeneralPaperFinalPolytopeCheck.run labels matrix S h auxiliary
      (reader (GeneralPaperRawAffineEvaluate.run false model 1 data auxNum auxDen).1)).accepted=true
  · simp only [run,Bool.false_eq_true,ite_false,hc,ite_true,Nat.mul_one]
    nlinarith only [ha,he,hca,hce]
  · simp only [run,Bool.false_eq_true,ite_false,hc,Nat.mul_one]
    nlinarith only [ha,hca]

end Blotto.GeneralPaperRawAffineEndpoint
