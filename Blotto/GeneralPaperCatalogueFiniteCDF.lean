import Blotto.GeneralPaperFourLossAlgebra
import Blotto.GeneralPaperCatalogueFullTrajectory

/-! Finite-code CDFs of the actual geometric execution. These finite
probability laws are analysis observers of the actual update history. The
runtime continues to query its own sparse trees and local arrays.
-/
namespace Blotto.GeneralPaperCatalogueFiniteCDF
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOccurrenceHistory GeneralPaperCatalogueGlobalLaw GeneralPaperCodeCDF
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def family {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) : Fin (2^(treeHeight learner a.lambda)) → ℝ :=
  GeneralPaperGeometricLevels.probability (GeneralPaperCachedMassJoin.base k) (history learner (prepare a k Qv weights Bc Br) a k j) time

theorem family_probability {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) : Probability (family learner a k Qv weights Bc Br time j) :=
  ⟨fun i => (GeneralPaperGeometricLevels.probability_positive (Nat.two_pow_pos _) _ (GeneralPaperCachedMassJoin.base_positive k) _ time i).le,
    GeneralPaperGeometricLevels.probability_sum (Nat.two_pow_pos _) _ (GeneralPaperCachedMassJoin.base_positive k) _ time⟩

theorem exact_prefix {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epochIndex : ℕ) (he : epochIndex≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (count : ℕ) (hc : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) (j : Fin m)
    (cut : ℕ) (hcut : cut≤2^(treeHeight learner a.lambda)) :
    prefixSum (family learner a k Qv weights Bc Br (epochIndex*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period+count) j) cut=
      GeneralPaperCatalogueExecutedErrors.cdf learner
        (GeneralPaperCatalogueOuterLoop.cacheAt (prepare a k Qv weights Bc Br) a k epochIndex) Qv weights Bc Br
        (GeneralPaperCatalogueGlobalErrors.incoming a k Qv weights Bc Br epochIndex he) count j cut := by
  rw [prefix_nat (Nat.two_pow_pos _) _ cut hcut]
  exact (GeneralPaperCatalogueGlobalErrors.incoming_cdf_global learner a k Qv weights Bc Br epochIndex he count hc j cut hcut).symm

theorem exact_time_prefix {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (j : Fin m)
    (cut : ℕ) (hcut : cut≤2^(treeHeight learner a.lambda)) :
    prefixSum (family learner a k Qv weights Bc Br time j) cut=
      GeneralPaperCatalogueExecutedErrors.cdf learner
        (GeneralPaperCatalogueOuterLoop.cacheAt (prepare a k Qv weights Bc Br) a k
          (time/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)) Qv weights Bc Br
        (GeneralPaperCatalogueGlobalErrors.incoming a k Qv weights Bc Br _
          (GeneralPaperCatalogueGlobalErrors.epoch_index_lt a.lambda k time ht).le)
        (time%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) j cut := by
  have he := exact_prefix learner a k Qv weights Bc Br _ (GeneralPaperCatalogueGlobalErrors.epoch_index_lt a.lambda k time ht).le
    _ (Nat.mod_lt time (GeneralPaperCatalogueGlobalHistory.period_positive a.lambda k)).le j cut hcut
  simpa only [GeneralPaperCatalogueFullTrajectory.time_partition] using he

end Blotto.GeneralPaperCatalogueFiniteCDF
