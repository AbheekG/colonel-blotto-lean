import Blotto.GeneralPaperCachedMeshIntervalQuery
import Blotto.GeneralPaperActualEpochSnapshotPrice

/-! Reached snapshots derive every mesh-prefix premise for all four
learners. Stored geometric powers, native local levels and the actual
snapshot construction supply numerator and total words without replay.
-/
namespace Blotto.GeneralPaperActualMeshPrefixInvariant
open GeneralPaperCatalogueEpochRun GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot
open GeneralPaperMeshPrefixInvariant (Good)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem occurrence_bound {k : ℕ} (state : State k) (bound : ℕ) (hState : Bounded state bound) (learner : Learner) :
    ∀ r,(occurrence learner state).read r≤bound := by
  cases learner with
  | p => exact hState.1
  | q => exact hState.2.1
  | lambda => exact hState.2.2.1
  | mu => exact hState.2.2.2.1

theorem block_positive {k : ℕ} (snapshot : Snapshot k) (hp : Positive snapshot) (learner : Learner) :
    (block learner snapshot).Positive := by
  cases learner with
  | p => exact hp.1
  | q => exact hp.2.1
  | lambda => exact hp.2.2.1
  | mu => exact hp.2.2.2

theorem block_coherent {k : ℕ} (snapshot : Snapshot k) (hc : Coherent snapshot) (learner : Learner) :
    (block learner snapshot).Coherent := by
  cases learner with
  | p => exact hc.1
  | q => exact hc.2.1
  | lambda => exact hc.2.2.1
  | mu => exact hc.2.2.2

theorem block_values {k : ℕ} (learner : Learner) (powers : GeneralPaperPreparedPowers.Prepared) (state : State k) :
    (block learner (take powers state)).values=GeneralPaperEpochPowerQueries.buildNumerators powers (occurrence learner state) := by
  cases learner <;> rfl

theorem take_values_bound (lambda k : ℕ) (state : State k)
    (hState : Bounded state (GeneralPaperPowerPrecision.levelBound lambda k)) (learner : Learner)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (block learner (take (GeneralPaperPreparedPowers.prepare lambda k) state)).values.read r≤
      4*(GeneralPaperPowerPrecision.prepare lambda k).unit := by
  rw [block_values,GeneralPaperEpochPowerQueries.read_numerators]
  exact GeneralPaperLocalNumeratorPrice.bound _ _ _
    (GeneralPaperPreparedPowers.query_certificate lambda k _ (occurrence_bound state _ hState learner r)).2.1

theorem take_good (m lambda k Qv : ℕ) (state : State k)
    (hState : Bounded state (GeneralPaperPowerPrecision.levelBound lambda k)) (learner : Learner) :
    Good m lambda k Qv (block learner (take (GeneralPaperPreparedPowers.prepare lambda k) state)).cdf :=
  GeneralPaperMeshPrefixInvariant.block_good m lambda k Qv _
    (block_positive _ (take_positive lambda k state hState) learner)
    (block_coherent _ (take_coherent _ state) learner) (take_values_bound lambda k state hState learner)

theorem selected_good {m k : ℕ} (cache : GeneralPaperCatalogueEpochCache.Cache m k) (Qv : ℕ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) (learner : Learner) :
    Good m cache.alphabet.lambda k Qv (block learner (snapshotAt (selected cache Qv weights Bc Br) time j)).cdf := by
  rw [snapshot_take]
  exact take_good m cache.alphabet.lambda k Qv _ (selected_cap cache Qv weights Bc Br time ht j) learner

theorem priced_good {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ)
    (cache : GeneralPaperCatalogueEpochCache.Cache m k) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) (learner : Learner) :
    Good m cache.alphabet.lambda k Qv (block learner ((GeneralPaperEpochSnapshotFamilyPrice.run bits index price W c
      (stateAt (selected cache Qv weights Bc Br) time).fields).1.read j)).cdf := by
  rw [GeneralPaperActualEpochSnapshotPrice.selected_data bits index price W Qv cache c hc]
  exact selected_good cache Qv weights Bc Br time ht j learner

end Blotto.GeneralPaperActualMeshPrefixInvariant
