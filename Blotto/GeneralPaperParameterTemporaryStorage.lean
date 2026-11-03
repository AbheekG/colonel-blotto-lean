import Blotto.GeneralPaperMaterializedCacheStorage

/-! Native child records held between parameter constructors: trajectory,
leaf, grid-width, profit-exponent and precision ceilings, the column ceiling,
minimum precision dyadic and trajectory dyadic. Full records include work
fields discarded from the eventual parameter cache. -/
namespace Blotto.GeneralPaperParameterTemporaryStorage
open GeneralPaperEncodedScalarStorage GeneralPaperScoreScaleParameters
open GeneralPaperPreparationCacheStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def footprint (W m lambda k Qv : ℕ) : ℕ :=
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  let s := GeneralPaperSourceParameters.prepare k
  powerFootprint W (GeneralPaperPowerCeiling.ceiling (GeneralPaperTrajectoryParameterPrice.target lambda k))+
    powerFootprint W (GeneralPaperPowerCeiling.ceiling m)+
    powerFootprint W (GeneralPaperPowerCeiling.ceiling (GeneralPaperProfitParameterPrice.widthTarget m k))+
    powerFootprint W (GeneralPaperPowerCeiling.ceiling (4*(2*t.rows*Qv*s.meshDenominator)))+
    powerFootprint W (GeneralPaperPowerCeiling.ceiling (GeneralPaperPrecisionParameterPrice.target lambda t.rows s.meshDenominator
      (powerRun (32+k)).power (powerRun (74+2*k)).power))+
    powerFootprint W (GeneralPaperPowerCeiling.ceiling (GeneralPaperPrecisionParameterPrice.level t.rows s.meshDenominator+1))+
    powerFootprint W (powerRun (74+2*k))+powerFootprint W (powerRun (35+k))+128*W

def profile (W m lambda k Qv : ℕ) : ℕ :=
  36*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+1408*W

theorem bounded (W m lambda k Qv : ℕ) : footprint W m lambda k Qv≤profile W m lambda k Qv := by
  have a := GeneralPaperCeilingConstructionStorage.source_record W m lambda k Qv
    (GeneralPaperTrajectoryParameterPrice.target lambda k) (Or.inr (Or.inl rfl))
  have b := GeneralPaperCeilingConstructionStorage.source_record W m lambda k Qv m (Or.inl rfl)
  have c := GeneralPaperCeilingConstructionStorage.source_record W m lambda k Qv
    (GeneralPaperProfitParameterPrice.widthTarget m k) (Or.inr (Or.inr (Or.inl rfl)))
  have d := GeneralPaperCeilingConstructionStorage.source_record W m lambda k Qv
    (4*(2*(GeneralPaperTrajectoryParameters.prepare lambda k).rows*Qv*(GeneralPaperSourceParameters.prepare k).meshDenominator))
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have e := GeneralPaperCeilingConstructionStorage.source_record W m lambda k Qv
    (GeneralPaperPrecisionParameterPrice.target lambda (GeneralPaperTrajectoryParameters.prepare lambda k).rows
      (GeneralPaperSourceParameters.prepare k).meshDenominator (powerRun (32+k)).power (powerRun (74+2*k)).power)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have f := GeneralPaperCeilingConstructionStorage.source_record W m lambda k Qv
    (GeneralPaperPrecisionParameterPrice.level (GeneralPaperTrajectoryParameters.prepare lambda k).rows
      (GeneralPaperSourceParameters.prepare k).meshDenominator+1)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have g := dyadic W m lambda k Qv (74+2*k) (Nat.le_refl _)
  have h := dyadic W m lambda k Qv (35+k) (by omega)
  unfold footprint profile
  dsimp only
  omega

end Blotto.GeneralPaperParameterTemporaryStorage
