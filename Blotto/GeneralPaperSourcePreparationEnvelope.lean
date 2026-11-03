import Blotto.GeneralPaperSourcePreparationSizes

/-! Collapse the complete cached parameter price to one explicit input
envelope. M is linear in k and logarithmic in lambda, m and Qv. Unit prices
give O(M) arithmetic; Rat prices give O(M*(W+Rat(4096*M))) bit work.
-/
namespace Blotto.GeneralPaperSourcePreparationEnvelope
open GeneralPaperSourcePreparationSizes GeneralPaperParameterOperandBounds
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

theorem base (m lambda k Qv : ℕ) :
    k+128≤measure m lambda k Qv ∧ 128≤measure m lambda k Qv := by
  unfold GeneralPaperSourcePreparationSizes.measure
  omega

theorem ceiling_profile (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv target : ℕ)
    (ht : binaryWordWidth target≤128*measure m lambda k Qv) :
    ceilingProfile primitive W target≤16384*measure m lambda k Qv*(W+primitive (width m lambda k Qv)) := by
  have hM := (base m lambda k Qv).2
  have hWord := ceiling_input_word target
  have hWidth : 1+binaryWordWidth (2*(target+1))≤width m lambda k Qv := by
    unfold width
    omega
  unfold ceilingProfile
  exact Nat.mul_le_mul
    (show 64*(binaryWordWidth target+1)≤16384*measure m lambda k Qv by omega)
    (Nat.add_le_add_left (hMono hWidth) W)

theorem trajectory_profile (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ) :
    GeneralPaperTrajectoryParameterPrice.profile primitive W lambda k≤
      32768*measure m lambda k Qv*(W+primitive (width m lambda k Qv)) := by
  let M := measure m lambda k Qv
  let F := W+primitive (width m lambda k Qv)
  have hb := sizes m lambda k Qv
  have hBase := (base m lambda k Qv).1
  have hc := ceiling_profile primitive hMono W m lambda k Qv (GeneralPaperTrajectoryParameterPrice.target lambda k)
    (by have hh:=hb.trajectoryTarget; omega)
  have hD : 8+2*(35+k)≤width m lambda k Qv := by have hh:=hb.dyadic; omega
  have hd := Nat.mul_le_mul
    (show 64*(35+k+1)≤128*M by dsimp only [M]; omega)
    (Nat.add_le_add_left (hMono hD) W)
  have hr := hMono hb.trajectoryRaw
  change _≤16384*M*F at hc
  change 64*(35+k+1)*(W+primitive (8+2*(35+k)))≤128*M*F at hd
  have hW : W≤F := Nat.le_add_right _ _
  have hP : primitive (width m lambda k Qv)≤F := Nat.le_add_left _ _
  have hMF : F≤M*F := by
    have hh : 1≤M := by dsimp only [M]; omega
    simpa only [one_mul] using Nat.mul_le_mul_right F hh
  unfold GeneralPaperTrajectoryParameterPrice.profile
  dsimp only
  change 64*(35+k+1)*(W+primitive (8+2*(35+k)))+
    ceilingProfile primitive W (GeneralPaperTrajectoryParameterPrice.target lambda k)+
    10*primitive (GeneralPaperTrajectoryParameterPrice.rawWidth lambda k
      (GeneralPaperScoreScaleParameters.powerRun (11+k)).power (GeneralPaperScoreScaleParameters.powerRun (35+k)).power
      (GeneralPaperPowerCeiling.ceiling (GeneralPaperTrajectoryParameterPrice.target lambda k)).power
      (GeneralPaperPowerCeiling.ceiling (GeneralPaperTrajectoryParameterPrice.target lambda k)).doublings
      (GeneralPaperScoreScaleParameters.powerRun (11+k)).doublings)+128*W≤32768*M*F
  nlinarith only [hc,hd,hr,hW,hP,hMF]

theorem profit_profile (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ) :
    GeneralPaperProfitParameterPrice.profile primitive W m lambda k Qv≤
      65536*measure m lambda k Qv*(W+primitive (width m lambda k Qv)) := by
  let M := measure m lambda k Qv
  let F := W+primitive (width m lambda k Qv)
  have hb := sizes m lambda k Qv
  have hBase := (base m lambda k Qv).1
  have hm := binaryWordWidth_mono (show m≤m+1 by omega)
  have hd : binaryWordWidth m≤128*M := by dsimp [M,GeneralPaperSourcePreparationSizes.measure]; omega
  have hl := ceiling_profile primitive hMono W m lambda k Qv m hd
  have hw := ceiling_profile primitive hMono W m lambda k Qv (GeneralPaperProfitParameterPrice.widthTarget m k)
    (by have hh:=hb.profitWidthTarget; omega)
  have he := ceiling_profile primitive hMono W m lambda k Qv
    (4*(2*(GeneralPaperTrajectoryParameters.prepare lambda k).rows*Qv*(GeneralPaperSourceParameters.prepare k).meshDenominator))
    (by have hh:=hb.profitExponentTarget; omega)
  have hr := hMono hb.profitRaw
  change _≤16384*M*F at hl hw he
  have hW : W≤F := Nat.le_add_right _ _
  have hP : primitive (width m lambda k Qv)≤F := Nat.le_add_left _ _
  have hMF : F≤M*F := by
    have hh : 1≤M := by dsimp only [M]; omega
    simpa only [one_mul] using Nat.mul_le_mul_right F hh
  unfold GeneralPaperProfitParameterPrice.profile
  dsimp only
  change _≤65536*M*F
  nlinarith only [hl,hw,he,hr,hW,hP,hMF]

theorem precision_profile (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ) :
    GeneralPaperPrecisionParameterPrice.profile primitive W lambda k≤
      65536*measure m lambda k Qv*(W+primitive (width m lambda k Qv)) := by
  let M := measure m lambda k Qv
  let F := W+primitive (width m lambda k Qv)
  have hb := sizes m lambda k Qv
  have hBase := (base m lambda k Qv).1
  have hp := ceiling_profile primitive hMono W m lambda k Qv _ hb.precisionTarget
  have hc := ceiling_profile primitive hMono W m lambda k Qv
    (GeneralPaperPrecisionParameterPrice.level (GeneralPaperTrajectoryParameters.prepare lambda k).rows
      (GeneralPaperSourceParameters.prepare k).meshDenominator+1) (by have hh:=hb.columnsTarget; omega)
  have hd := Nat.mul_le_mul
    (show 64*(74+2*k+1)≤128*M by dsimp only [M]; omega)
    (Nat.add_le_add_left (hMono hb.dyadic) W)
  have hr := hMono hb.precisionRaw
  change _≤16384*M*F at hp hc
  change 64*(74+2*k+1)*(W+primitive (8+2*(74+2*k)))≤128*M*F at hd
  have hW : W≤F := Nat.le_add_right _ _
  have hP : primitive (width m lambda k Qv)≤F := Nat.le_add_left _ _
  have hMF : F≤M*F := by
    have hh : 1≤M := by dsimp only [M]; omega
    simpa only [one_mul] using Nat.mul_le_mul_right F hh
  unfold GeneralPaperPrecisionParameterPrice.profile
  dsimp only
  change _≤65536*M*F
  nlinarith only [hp,hc,hd,hr,hW,hP,hMF]

theorem profile_bound (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ) :
    GeneralPaperSourcePreparationCache.profile primitive W m lambda k Qv≤
      262144*measure m lambda k Qv*(W+primitive (width m lambda k Qv)) := by
  let M := measure m lambda k Qv
  let F := W+primitive (width m lambda k Qv)
  have hb := (sizes m lambda k Qv).source
  have hBase := (base m lambda k Qv).1
  have hs : GeneralPaperSourceParameterPrice.profile primitive W k≤512*M*F := by
    unfold GeneralPaperSourceParameterPrice.profile
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 512 (by dsimp only [M]; omega : k+35≤M))
      (Nat.add_le_add_left (hMono hb) W)
  have ht := trajectory_profile primitive hMono W m lambda k Qv
  have hp := profit_profile primitive hMono W m lambda k Qv
  have hf := precision_profile primitive hMono W m lambda k Qv
  change _≤32768*M*F at ht
  change _≤65536*M*F at hp hf
  have hW : W≤F := Nat.le_add_right _ _
  have hMF : F≤M*F := by
    have hh : 1≤M := by dsimp only [M]; omega
    simpa only [one_mul] using Nat.mul_le_mul_right F hh
  unfold GeneralPaperSourcePreparationCache.profile
  change _≤262144*M*F
  nlinarith only [hs,ht,hp,hf,hW,hMF]

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ) :
    (GeneralPaperSourcePreparationCache.prepare primitive W m lambda k Qv).2≤
      262144*measure m lambda k Qv*(W+primitive (width m lambda k Qv)) :=
  (GeneralPaperSourcePreparationCache.work primitive hMono W m lambda k Qv).trans (profile_bound primitive hMono W m lambda k Qv)

theorem unit_work (m lambda k Qv : ℕ) :
    (GeneralPaperSourcePreparationCache.prepare (fun _ => 1) 1 m lambda k Qv).2≤524288*measure m lambda k Qv := by
  have h := work (fun _ => 1) (by intro a b hab; rfl) 1 m lambda k Qv
  exact h.trans (by change 262144*measure m lambda k Qv*2≤524288*measure m lambda k Qv; omega)

end Blotto.GeneralPaperSourcePreparationEnvelope
