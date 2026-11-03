import Blotto.GeneralPaperCatalogueGlobalErrors

/-! Both actual whole-row optimizers obey beta_opt at every global
iteration. The preceding forest, summary/error certificates and common
snapshot are all obtained from the same outer execution. Literal feasible
comparators remain explicit; the continuous-response join is separate.
-/
namespace Blotto.GeneralPaperCatalogueGlobalOptimizer
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def score {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (codes : FixedArrayTable m ℕ) : ℝ :=
  GeneralPaperCatalogueTrueScore.trueScore response
    (cacheAt (prepare a k Qv weights Bc Br) a k (time/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)) Qv weights Bc Br
    (GeneralPaperCatalogueGlobalErrors.incoming a k Qv weights Bc Br _ (GeneralPaperCatalogueGlobalErrors.epoch_index_lt a.lambda k time ht).le)
    (time%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) codes

def chosen {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ) : FixedArrayTable m ℕ :=
  GeneralPaperCatalogueTrueScore.chosenCodes response
    (epochRun (prepare a k Qv weights Bc Br) a k
      (treesAt (prepare a k Qv weights Bc Br) a k (time/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)))
    (time%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)

theorem optimality {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ) (time : ℕ)
    (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (codes : FixedArrayTable m ℕ)
    (choices : FixedArrayTable m Choice) (hDecode : ∀ j, (GeneralPaperCodeDecode.decode a response (codes.read j)).choice=some (choices.read j))
    (hBudget : (∑ j, (choices.read j).tag)≤GeneralPaperResponseTag.budget (if response then Br else Bc)) :
    score response a k Qv weights Bc Br time ht codes-
      score response a k Qv weights Bc Br time ht (chosen response a k Qv weights Bc Br time)≤
        25*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/16 := by
  have he := (GeneralPaperCatalogueGlobalErrors.epoch_index_lt a.lambda k time ht).le
  exact GeneralPaperCatalogueTrueScore.tree_optimality response a k _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br _ he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br _ he)
    Qv hQv weights hWeights Bc Br _ (Nat.mod_lt time (GeneralPaperCatalogueGlobalHistory.period_positive a.lambda k)).le
    codes choices hDecode hBudget

end Blotto.GeneralPaperCatalogueGlobalOptimizer
