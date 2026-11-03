import Blotto.GeneralPaperLocalTrajectoryStorage

/-! Resident data at a reached pre-update epoch point coexist: current
forest/cache/levels, common snapshot, retained global rows and the local
row prefix. The retained shared power/profit preparation, selector/query
temporaries and primitive scratch are separate remaining workspaces. -/
namespace Blotto.GeneralPaperEpochResidentStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueEpochRun
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def footprint {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ) : ℕ :=
  let shared := prepare a k Qv weights Bc Br
  let trees := treesAt shared a k epoch
  let cache := GeneralPaperCatalogueShared.cache shared a k trees
  let current := GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br
  GeneralPaperEncodedForestStorage.footprint W trees+GeneralPaperEncodedEpochCache.footprint W cache+
    GeneralPaperEncodedEpochLevels.familyFootprint W (stateAt current time).fields+
    GeneralPaperEncodedSnapshotStorage.familyFootprint W (beforeAt current time)+
    GeneralPaperEncodedTrajectoryStorage.footprint W shared.trajectory.rows (execute shared a k epoch).2+
    GeneralPaperEncodedTrajectoryStorage.footprint W shared.trajectory.period
      (GeneralPaperCatalogueEpoch.execute cache current.powers current.profit current.T weights Bc Br
        (GeneralPaperCatalogueEpochCache.initial cache) time).2

def profile (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperEncodedForestStorage.profile W m lambda k Qv+GeneralPaperEncodedEpochCache.profile W m lambda k+
    GeneralPaperEncodedEpochLevels.profile W m lambda k Qv+GeneralPaperEncodedSnapshotStorage.profile W m lambda k Qv+
    GeneralPaperEncodedTrajectoryStorage.profile W m lambda k+GeneralPaperLocalTrajectoryStorage.profile W m lambda k

theorem actual {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    footprint W k Qv a weights Bc Br epoch time≤profile W m a.lambda k Qv := by
  let shared := prepare a k Qv weights Bc Br
  let cache := GeneralPaperCatalogueShared.cache shared a k (treesAt shared a k epoch)
  have hf := GeneralPaperEncodedForestStorage.actual W k Qv a weights Bc Br epoch he
  have hc := GeneralPaperActualEpochCacheStorage.epoch W k Qv a weights Bc Br epoch
  have hl := GeneralPaperEncodedEpochLevels.selected W Qv cache weights Bc Br time ht
  have hs := GeneralPaperEncodedSnapshotStorage.selected W Qv cache weights Bc Br time ht
  have ho := GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights Bc Br epoch he
  have hp := GeneralPaperLocalTrajectoryStorage.selected W Qv cache weights Bc Br time ht
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hf hc) hl) hs) ho) hp

theorem retained_first_trajectory {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ)
    (Bc Br firstBc firstBr : ℚ) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    let first := prepare a k Qv weights firstBc firstBr
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows (execute first a k first.trajectory.epochs).2+
      footprint W k Qv a weights Bc Br epoch time≤
        GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+profile W m a.lambda k Qv :=
  Nat.add_le_add (GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights firstBc firstBr _ (Nat.le_refl _))
    (actual W k Qv a weights Bc Br epoch time he ht)

end Blotto.GeneralPaperEpochResidentStorage
