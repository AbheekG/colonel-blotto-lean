import Blotto.GeneralPaperCatalogueExecutedErrors

/-! Shared preparation for the concrete outer loop. Powers, optimizer
parameters, trajectory controls, comparison width and root spans are built
once and passed by reference to every epoch. Local selected-run identities
are proof equalities; they introduce no repeated source preparation.
-/
namespace Blotto.GeneralPaperCatalogueShared
open GeneralPaperCodeAlphabet GeneralPaperCatalogueEpochCache GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOccurrenceHistory
set_option autoImplicit false

structure Shared (m : ℕ) where
  powers : GeneralPaperPreparedPowers.Prepared
  profit : GeneralPaperProfitParameters.Prepared
  trajectory : GeneralPaperTrajectoryParameters.Parameters
  wordWidth : ℕ
  unsignedSpan : ℚ
  signedSpan : ℚ
  weights : FixedArrayTable m ℕ
  Bc : ℚ
  Br : ℚ

def prepare {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : Shared m :=
  let unsignedSpan : ℚ := 8*a.C
  ⟨GeneralPaperPreparedPowers.prepare a.lambda k,GeneralPaperProfitParameters.prepare m a.lambda k Qv,
    GeneralPaperTrajectoryParameters.prepare a.lambda k,GeneralPaperQuantileComparison.width a.lambda k,
    unsignedSpan,2*unsignedSpan,weights,Bc,Br⟩

def span {m : ℕ} (learner : Learner) (shared : Shared m) : ℚ :=
  match learner with
  | .p | .q => shared.unsignedSpan
  | .lambda | .mu => shared.signedSpan

def cache {m : ℕ} (shared : Shared m) (a : Alphabet) (k : ℕ) (trees : Trees m a.lambda) : Cache m k :=
  GeneralPaperCatalogueTreeCache.prepare shared.powers shared.wordWidth a k trees

def epochRun {m : ℕ} (shared : Shared m) (a : Alphabet) (k : ℕ) (trees : Trees m a.lambda) :
    GeneralPaperCatalogueEpochRun.Run (cache shared a k trees) :=
  ⟨shared.powers,shared.profit,shared.trajectory.rows,shared.weights,shared.Bc,shared.Br⟩

theorem cache_alphabet {m : ℕ} (shared : Shared m) (a : Alphabet) (k : ℕ) (trees : Trees m a.lambda) :
    (cache shared a k trees).alphabet=a := rfl

theorem epochRun_selected {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (trees : Trees m a.lambda) :
    epochRun (prepare a k Qv weights Bc Br) a k trees=
      GeneralPaperCatalogueEpochRun.selected (cache (prepare a k Qv weights Bc Br) a k trees) Qv weights Bc Br := rfl

theorem prepared_period {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (prepare a k Qv weights Bc Br).trajectory.period=(GeneralPaperTrajectoryParameters.prepare a.lambda k).period := rfl

theorem span_power {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    span learner (prepare a k Qv weights Bc Br)=(2:ℚ)^(treeHeight learner a.lambda) := by
  have hu : (8:ℚ)*a.C=(2:ℚ)^a.lambda := by exact_mod_cast a.dyadic
  cases learner <;> simp only [span,prepare,treeHeight] <;> rw [hu]
  all_goals rw [pow_succ]; ring

end Blotto.GeneralPaperCatalogueShared
