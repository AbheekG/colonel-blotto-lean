import Blotto.GeneralPaperRawAffineBits
import Blotto.GeneralPaperFinalPolytopeBits
import Blotto.GeneralPaperRawAffineEndpoint

/-! Both final rechecks now use the complete bit-priced original static
scan and strict-score DP. A rejected auxiliary point skips the endpoint.
All operand premises are derived from the raw fractions and affine cache,
so neither check assumes its candidate point has already been accepted. -/
namespace Blotto.GeneralPaperRawEndpointBits
open GeneralPaperBasisAffineData GeneralPaperBasisOriginalDirection GeneralPaperRayRationalBound
set_option autoImplicit false
set_option maxHeartbeats 6000000

def run {T m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ)
    (cache : Data (m*(K-1))) : GeneralPaperCheckedAffineEndpoint.Result (m*(K-1)) :=
  let aux := GeneralPaperRawAffineEvaluate.run true model W cache auxNum auxDen
  let checkAux := GeneralPaperFinalPolytopeBits.run model W labels matrix S h auxiliary (reader aux.1)
  if checkAux.accepted then
    let endpoint := GeneralPaperRawAffineEvaluate.run true model W cache endNum endDen
    let checkEnd := GeneralPaperFinalPolytopeBits.run model W labels matrix S h gamma (reader endpoint.1)
    ⟨if checkEnd.accepted then some endpoint.1 else none,aux.2+checkAux.work+endpoint.2+checkEnd.work+16*W⟩
  else ⟨none,aux.2+checkAux.work+8*W⟩

theorem data {T m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ)
    (cache : Data (m*(K-1))) :
    (run model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache).point=
      (GeneralPaperRawAffineEndpoint.run true model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache).point := by
  simp only [run,GeneralPaperRawAffineEndpoint.run,GeneralPaperFinalPolytopeBits.data]
  split <;> rfl

theorem represented {T m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ)
    (hAuxDen : 0<auxDen) (hEndDen : 0<endDen)
    (hAux : (auxNum:ℚ)/(auxDen:ℚ)=auxiliary) (hEnd : (endNum:ℚ)/(endDen:ℚ)=gamma)
    (cache : Data (m*(K-1))) :
    (run model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache).point=
      (GeneralPaperCheckedAffineEndpoint.run labels matrix S h auxiliary gamma cache).point := by
  rw [data]
  exact GeneralPaperRawAffineEndpoint.point true model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen
    hAuxDen hEndDen hAux hEnd cache

theorem cache_congr {T m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ)
    (left right : Data (m*(K-1))) (hc : left.constant=right.constant) (hs : left.slope=right.slope)
    (hd : left.determinant=right.determinant) :
    run model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen left=
      run model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen right := by
  simp only [run,GeneralPaperRawAffineBits.cache_congr true model W left right hc hs hd]

def evaluationProfile (model : RationalCostModel) (W T m K S H B N D : ℕ) : ℕ :=
  256*(m*(K-1)+1)*(W+model.rat (GeneralPaperRawAffineBits.width H B N))+
    GeneralPaperFinalPolytopeBits.profile T m K S W
      (model.rat (1+2*(GeneralPaperRayUniformSize.width D 1 m ((N+B)*H) 0 B+1)))

theorem evaluationProfile_den_mono (model : RationalCostModel) (W T m K S H B N D E : ℕ) (hDE : D≤E) :
    evaluationProfile model W T m K S H B N D≤evaluationProfile model W T m K S H B N E := by
  have hd := binaryWordWidth_mono hDE
  have hw : 1+2*(GeneralPaperRayUniformSize.width D 1 m ((N+B)*H) 0 B+1)≤
      1+2*(GeneralPaperRayUniformSize.width E 1 m ((N+B)*H) 0 B+1) := by
    dsimp only [GeneralPaperRayUniformSize.width,GeneralPaperRayAffineBound.rootWidth]
    omega
  have hp := model.monotone hw
  unfold evaluationProfile GeneralPaperFinalPolytopeBits.profile GeneralPaperStaticScanPrice.profile
  gcongr

theorem evaluation_work {T m K : ℕ} (model : RationalCostModel) (W H B N : ℕ) (hm : 0<m)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (beta : ℚ) (numerator : ℤ) (denominator : ℕ) (hDen : 0<denominator)
    (hBeta : (numerator:ℚ)/(denominator:ℚ)=beta) (cache : Data (m*(K-1)))
    (hDet : cache.determinant≠0) (hd : cache.determinant.natAbs≤H)
    (hc : ∀ k,(cache.constant.read k).natAbs≤H) (hs : ∀ k,(cache.slope.read k).natAbs≤H)
    (hb : numerator.natAbs≤B) (hn : denominator≤N) (hW : 1≤W)
    (hD : binaryWordWidth (m*(K-1)+1)≤W) (hK : binaryWordWidth (K+1)≤W)
    (hM : binaryWordWidth (m+1)≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (GeneralPaperRawAffineEvaluate.run true model W cache numerator denominator).2+
      (GeneralPaperFinalPolytopeBits.run model W labels matrix S h beta
        (reader (GeneralPaperRawAffineEvaluate.run true model W cache numerator denominator).1)).work≤
          evaluationProfile model W T m K S H B N (denominator*cache.determinant.natAbs) := by
  have he := GeneralPaperRawAffineBits.work model W H B N hW hD cache numerator denominator hb hn hd hc hs
  have hx (a : RationalOrderCell.Variable m K) := GeneralPaperRawAffineBits.bounded model W H B N cache numerator denominator
    hDen hDet hb hn hc hs (GeneralPaperBasisCoordinates.index a)
  have hb' := GeneralPaperRawAffineBits.threshold_bounded numerator denominator hDen cache.determinant.natAbs B hb
  rw [hBeta] at hb'
  have hDPos := Nat.mul_pos hDen (Int.natAbs_pos.mpr hDet)
  have hCheck := GeneralPaperFinalPolytopeBits.work model W (denominator*cache.determinant.natAbs) ((N+B)*H) B
    hm hDPos labels matrix S h beta hb' (reader (GeneralPaperRawAffineEvaluate.run true model W cache numerator denominator).1)
    hx hW hK hM hIndex
  exact Nat.add_le_add he hCheck

theorem work {T m K : ℕ} (model : RationalCostModel) (W H Ba Na Be Ne : ℕ) (hm : 0<m)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ)
    (hAuxDen : 0<auxDen) (hEndDen : 0<endDen)
    (hAux : (auxNum:ℚ)/(auxDen:ℚ)=auxiliary) (hEnd : (endNum:ℚ)/(endDen:ℚ)=gamma)
    (cache : Data (m*(K-1))) (hDet : cache.determinant≠0) (hd : cache.determinant.natAbs≤H)
    (hc : ∀ k,(cache.constant.read k).natAbs≤H) (hs : ∀ k,(cache.slope.read k).natAbs≤H)
    (hAN : auxNum.natAbs≤Ba) (hAD : auxDen≤Na) (hEN : endNum.natAbs≤Be) (hED : endDen≤Ne)
    (hW : 1≤W) (hD : binaryWordWidth (m*(K-1)+1)≤W) (hK : binaryWordWidth (K+1)≤W)
    (hM : binaryWordWidth (m+1)≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (run model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen cache).work≤
      evaluationProfile model W T m K S H Ba Na (auxDen*cache.determinant.natAbs)+
      evaluationProfile model W T m K S H Be Ne (endDen*cache.determinant.natAbs)+16*W := by
  have ha := evaluation_work model W H Ba Na hm labels matrix S h auxiliary auxNum auxDen hAuxDen hAux cache
    hDet hd hc hs hAN hAD hW hD hK hM hIndex
  have he := evaluation_work model W H Be Ne hm labels matrix S h gamma endNum endDen hEndDen hEnd cache
    hDet hd hc hs hEN hED hW hD hK hM hIndex
  by_cases hCheck : (GeneralPaperFinalPolytopeBits.run model W labels matrix S h auxiliary
      (reader (GeneralPaperRawAffineEvaluate.run true model W cache auxNum auxDen).1)).accepted=true
  · simp only [run,hCheck,ite_true]
    omega
  · simp only [run,hCheck,Bool.false_eq_true,ite_false]
    omega

end Blotto.GeneralPaperRawEndpointBits
