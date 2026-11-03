import Blotto.GeneralPaperCatalogueGlobalCDF
import Blotto.GeneralPaperCatalogueOuterTrajectory

/-! Global true losses and integer-update errors for the actual execution.
Incoming-law certificates are derived from its own preceding epochs. Beyond
the proved forest horizon the mathematical true-loss observer is extended
by executed loss; this observer is never called by the runtime source.
-/
namespace Blotto.GeneralPaperCatalogueGlobalErrors
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory GeneralPaperCatalogueGlobalLaw
open GeneralPaperGeometricLevels
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

noncomputable def incoming {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epochIndex : ℕ) (he : epochIndex≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    GeneralPaperCatalogueIncoming.Incoming (cacheAt (prepare a k Qv weights Bc Br) a k epochIndex) :=
  GeneralPaperCatalogueIncoming.fromTrees a k (treesAt (prepare a k Qv weights Bc Br) a k epochIndex)
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epochIndex he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epochIndex he)

theorem epoch_index_lt (lambda k time : ℕ) (ht : time<(GeneralPaperTrajectoryParameters.prepare lambda k).rows) :
    time/(GeneralPaperTrajectoryParameters.prepare lambda k).period<(GeneralPaperTrajectoryParameters.prepare lambda k).epochs := by
  apply (Nat.div_lt_iff_lt_mul (GeneralPaperCatalogueGlobalHistory.period_positive lambda k)).mpr
  exact ht

noncomputable def truth {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) (i : Fin (2^(treeHeight learner a.lambda))) : ℝ :=
  let period := (GeneralPaperTrajectoryParameters.prepare a.lambda k).period
  if he : time/period≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs then
    GeneralPaperCatalogueExecutedErrors.exactLoss learner (cacheAt (prepare a k Qv weights Bc Br) a k (time/period)) Qv weights Bc Br
      (incoming a k Qv weights Bc Br (time/period) he) (time%period) j i.val
  else (executedLoss (GeneralPaperSourceParameters.prepare k).theta (history learner (prepare a k Qv weights Bc Br) a k j time i):ℝ)

theorem error_bound {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) (i : Fin (2^(treeHeight learner a.lambda))) :
    |truth learner a k Qv weights Bc Br time j i-
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (history learner (prepare a k Qv weights Bc Br) a k j time i):ℝ)|≤
      49*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/128 := by
  unfold truth
  dsimp only
  split_ifs with he
  · exact GeneralPaperCatalogueExecutedErrors.tree_error_bound learner a k _
      (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br _ he)
      (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br _ he)
      Qv weights Bc Br _ (Nat.mod_lt time (GeneralPaperCatalogueGlobalHistory.period_positive a.lambda k)).le j i.val i.isLt
  · rw [sub_self,abs_zero]
    have hp : (0:ℝ)<(GeneralPaperSourceParameters.prepare k).eta := by exact_mod_cast (GeneralPaperSourceParameters.positive k).2.1
    positivity

theorem truth_actual {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (j : Fin m)
    (i : Fin (2^(treeHeight learner a.lambda))) :
    truth learner a k Qv weights Bc Br time j i=
      GeneralPaperCatalogueExecutedErrors.exactLoss learner
        (cacheAt (prepare a k Qv weights Bc Br) a k (time/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)) Qv weights Bc Br
        (incoming a k Qv weights Bc Br _ (epoch_index_lt a.lambda k time ht).le)
        (time%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) j i.val := by
  unfold truth
  rw [dif_pos (epoch_index_lt a.lambda k time ht).le]

theorem incoming_cdf_global {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epochIndex : ℕ) (he : epochIndex≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (count : ℕ) (hc : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) (j : Fin m)
    (cut : ℕ) (hcut : cut≤2^(treeHeight learner a.lambda)) :
    GeneralPaperCatalogueExecutedErrors.cdf learner (cacheAt (prepare a k Qv weights Bc Br) a k epochIndex) Qv weights Bc Br
      (incoming a k Qv weights Bc Br epochIndex he) count j cut=
      GeneralPaperOrderedVariation.prefixMass
        (fun i => probability (GeneralPaperCachedMassJoin.base k) (history learner (prepare a k Qv weights Bc Br) a k j)
          (epochIndex*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period+count)
          (GeneralPaperGeometricVariation.code (Nat.two_pow_pos (treeHeight learner a.lambda)) i)) cut :=
  GeneralPaperCatalogueGlobalCDF.current_global learner a k Qv weights Bc Br epochIndex he count hc j cut hcut

end Blotto.GeneralPaperCatalogueGlobalErrors
