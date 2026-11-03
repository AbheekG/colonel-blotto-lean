import Blotto.GeneralPaperParameterTemporaryStorage
import Blotto.GeneralPaperSharedResidentStorage

/-! Parameter/power preparation reservations and the additional retained
materialization cache join actual native returns and source residents.
Parameter raw-primitive scratch uses its complete operation allowance;
child records and recursive doubling/ceiling frames are counted separately.
Grid sorting/construction, the classifier front end and global W remain
separate obligations. -/
namespace Blotto.GeneralPaperPreparationResidentStorage
open GeneralPaperSourcePreparationSizes
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def dyadicProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  (74+2*k+1)*(4*H+192*W)+64*(74+2*k+1)*(W+model.rat H)

def ceilingProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  (128*measure m lambda k Qv+1)*(5*H+192*W)+64*(128*measure m lambda k Qv+1)*(W+model.rat H)

def constructionWindow (model : RationalCostModel) (W m lambda k Qv columns exponent target : ℕ) : ℕ :=
  let c := (GeneralPaperSourcePreparationCache.prepare model.rat W m lambda k Qv).1
  GeneralPaperPreparationCacheStorage.footprint W c+GeneralPaperParameterTemporaryStorage.footprint W m lambda k Qv+
    GeneralPaperPowerConstructionStorage.window model W k c columns+
    max (GeneralPaperDyadicConstructionStorage.window model W exponent) (GeneralPaperCeilingConstructionStorage.window model W target)+
    (GeneralPaperSourcePreparationCache.prepare model.rat W m lambda k Qv).2

def constructionProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperPreparationCacheStorage.profile W m lambda k Qv+GeneralPaperParameterTemporaryStorage.profile W m lambda k Qv+
    GeneralPaperPowerConstructionStorage.profile model W m lambda k Qv+
    max (dyadicProfile model W m lambda k Qv) (ceilingProfile model W m lambda k Qv)+
    262144*measure m lambda k Qv*(W+model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv))

theorem construction (model : RationalCostModel) (W m lambda k Qv columns exponent target : ℕ)
    (hc : columns≤(GeneralPaperPowerPrecision.prepare lambda k).columns) (he : exponent≤74+2*k)
    (ht : GeneralPaperSourcePreparationControls.IsTarget m lambda k Qv target) :
    constructionWindow model W m lambda k Qv columns exponent target≤constructionProfile model W m lambda k Qv := by
  have hCache := GeneralPaperPreparationCacheStorage.returned model.rat W m lambda k Qv
  have hTemps := GeneralPaperParameterTemporaryStorage.bounded W m lambda k Qv
  have hPowers := GeneralPaperPowerConstructionStorage.bounded model W m lambda k Qv _
    (GeneralPaperSourcePreparationCache.data model.rat W m lambda k Qv) columns hc
  have hD := GeneralPaperDyadicConstructionStorage.whole model W m lambda k Qv exponent he
  have hDyadic : GeneralPaperDyadicConstructionStorage.window model W exponent≤dyadicProfile model W m lambda k Qv :=
    hD.trans (Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.add_le_add_right he 1))
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 64 (Nat.add_le_add_right he 1))))
  have hCeiling := GeneralPaperCeilingConstructionStorage.source model W m lambda k Qv target ht
  have hScratch := (GeneralPaperSourcePreparationCache.work model.rat model.monotone W m lambda k Qv).trans
    (GeneralPaperSourcePreparationEnvelope.profile_bound model.rat model.monotone W m lambda k Qv)
  have hWidth : width m lambda k Qv≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    unfold width GeneralPaperPowerPreparationEnvelope.operandWidth
    omega
  have hS := hScratch.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hWidth) W))
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hCache hTemps) hPowers)
    (max_le_max hDyadic hCeiling)) hS

def residentProfile {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  GeneralPaperMaterializedCacheStorage.gridProfile W m a.lambda k Qv+
    GeneralPaperEncodedSharedSource.profile W k Qv a weights Bc Br+GeneralPaperEpochResidentStorage.profile W m a.lambda k Qv

theorem resident {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    GeneralPaperMaterializedCacheStorage.gridFootprint W (GeneralPaperMaterializedGridCache.specification m a.lambda k Qv)+
      GeneralPaperEncodedSharedSource.footprint W (prepare a k Qv weights Bc Br)+
      GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch time≤residentProfile W k Qv a weights Bc Br :=
  Nat.add_le_add (Nat.add_le_add (GeneralPaperMaterializedCacheStorage.grid_native W m a.lambda k Qv)
    (GeneralPaperEncodedSharedSource.native W k Qv a weights Bc Br))
    (GeneralPaperEpochResidentStorage.actual W k Qv a weights Bc Br epoch time he ht)

theorem prepared_resident {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    GeneralPaperMaterializedCacheStorage.gridFootprint W ready.2+GeneralPaperEncodedSharedSource.footprint W ready.1.2+
      GeneralPaperEpochResidentStorage.footprint W k Qv ready.1.1.1.2 weights Bc Br epoch time≤
      residentProfile W k Qv ready.1.1.1.2 weights Bc Br := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact resident W k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br epoch time he ht

theorem retained_first_trajectory {m : ℕ} (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    let first := prepare a k Qv weights firstBc firstBr
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows
        (GeneralPaperCatalogueOuterLoop.execute first a k first.trajectory.epochs).2+
      (GeneralPaperMaterializedCacheStorage.gridFootprint W (GeneralPaperMaterializedGridCache.specification m a.lambda k Qv)+
        GeneralPaperEncodedSharedSource.footprint W (prepare a k Qv weights Bc Br)+
        GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch time)≤
      GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+residentProfile W k Qv a weights Bc Br :=
  Nat.add_le_add (GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights firstBc firstBr _ (Nat.le_refl _))
    (resident W k Qv a weights Bc Br epoch time he ht)

end Blotto.GeneralPaperPreparationResidentStorage
