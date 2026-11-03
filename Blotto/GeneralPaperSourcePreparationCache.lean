import Blotto.GeneralPaperPrecisionParameterPrice

/-! One complete parameter cache for the selected source. The source
constants, trajectory, profit parameters and floating precision are returned
together. Period/alpha/nu controls and native work annotations are reused
from these returned records; parameter construction is not replayed.
This is parameter preparation, before grid/power-table materialization.
-/
namespace Blotto.GeneralPaperSourcePreparationCache
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

structure Cache where
  denominators : GeneralPaperSourceParameterPrice.Cache
  source : GeneralPaperSourceParameters.Parameters
  trajectory : GeneralPaperTrajectoryParameters.Parameters
  profit : GeneralPaperProfitParameters.Parameters
  precision : GeneralPaperPrecisionParameterPrice.Output

def specification (m lambda k Qv : ℕ) : Cache :=
  ⟨GeneralPaperSourceParameterPrice.specification k,GeneralPaperSourceParameters.prepare k,
    GeneralPaperTrajectoryParameters.prepare lambda k,GeneralPaperProfitParameters.parameters m lambda k Qv,
    GeneralPaperPrecisionParameterPrice.specification lambda k⟩

def prepare (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) : Cache × ℕ :=
  let source := GeneralPaperSourceParameterPrice.run primitive W k
  let trajectory := GeneralPaperTrajectoryParameterPrice.fromCache primitive W lambda k source.1.1
  let profit := GeneralPaperProfitParameterPrice.fromCache primitive W m Qv source.1.1 source.1.2 trajectory.1
  let precision := GeneralPaperPrecisionParameterPrice.fromCache primitive W lambda k source.1.1 source.1.2 trajectory.1
  (⟨source.1.1,source.1.2,trajectory.1,profit.1,precision.1⟩,
    source.2+trajectory.2+profit.2+precision.2+96*W)

theorem data (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) :
    (prepare primitive W m lambda k Qv).1=specification m lambda k Qv := by
  unfold prepare
  dsimp only
  rw [GeneralPaperSourceParameterPrice.data,
    GeneralPaperTrajectoryParameterPrice.data primitive W lambda k _ rfl,
    GeneralPaperProfitParameterPrice.data primitive W m lambda k Qv _ rfl _ rfl _ rfl,
    GeneralPaperPrecisionParameterPrice.data primitive W lambda k _ rfl _ rfl _ rfl]
  rfl

def profile (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperSourceParameterPrice.profile primitive W k+
    GeneralPaperTrajectoryParameterPrice.profile primitive W lambda k+
    GeneralPaperProfitParameterPrice.profile primitive W m lambda k Qv+
    GeneralPaperPrecisionParameterPrice.profile primitive W lambda k+96*W

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ) :
    (prepare primitive W m lambda k Qv).2≤profile primitive W m lambda k Qv := by
  let s := GeneralPaperSourceParameterPrice.run primitive W k
  let t := GeneralPaperTrajectoryParameterPrice.fromCache primitive W lambda k s.1.1
  have hs := GeneralPaperSourceParameterPrice.data primitive W k
  have hd : s.1.1=GeneralPaperSourceParameterPrice.specification k := congrArg Prod.fst hs
  have hp : s.1.2=GeneralPaperSourceParameters.prepare k := congrArg Prod.snd hs
  have ht := GeneralPaperTrajectoryParameterPrice.data primitive W lambda k s.1.1 hd
  have h1 := GeneralPaperSourceParameterPrice.work primitive hMono W k
  have h2 := GeneralPaperTrajectoryParameterPrice.work primitive hMono W lambda k s.1.1 hd
  have h3 := GeneralPaperProfitParameterPrice.work primitive hMono W m lambda k Qv s.1.1 hd s.1.2 hp t.1 ht
  have h4 := GeneralPaperPrecisionParameterPrice.work primitive hMono W lambda k s.1.1 hd s.1.2 hp t.1 ht
  change s.2+t.2+(GeneralPaperProfitParameterPrice.fromCache primitive W m Qv s.1.1 s.1.2 t.1).2+
    (GeneralPaperPrecisionParameterPrice.fromCache primitive W lambda k s.1.1 s.1.2 t.1).2+96*W≤_
  unfold profile
  change s.2≤_ at h1
  change t.2≤_ at h2
  omega

theorem both_data (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) :
    (prepare primitive W m lambda k Qv).1=(prepare (fun _ => 1) 1 m lambda k Qv).1 := by rw [data,data]

theorem returned_controls (primitive : ℕ → ℕ) (W m lambda k Qv : ℕ) :
    let c := (prepare primitive W m lambda k Qv).1
    c.trajectory.period=c.denominators.zDen.power ∧
      c.source.meshDenominator=c.denominators.thetaDen.power ∧
      c.precision.levelBound=8*c.trajectory.rows*c.source.meshDenominator ∧
      c.precision.errorFactor=16*(c.precision.levelBound+1)*(lambda+2) ∧
      c.profit.qProf=2*c.trajectory.rows*Qv*c.source.meshDenominator := by
  rw [data]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end Blotto.GeneralPaperSourcePreparationCache
