import Blotto.GeneralPaperCatalogueGlobalHistory

/-! The actual outer forest represents the single global geometric law,
with all previous epochs' levels retained. Dense sums in these identities
are mathematical observers, not operations of the compressed source.
-/
namespace Blotto.GeneralPaperCatalogueGlobalLaw
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory GeneralPaperIntervalLevels
open GeneralPaperCatalogueGlobalHistory
set_option autoImplicit false
set_option maxHeartbeats 3500000

def history {m : ℕ} (learner : Learner) (shared : Shared m) (a : Alphabet) (k : ℕ) (j : Fin m) :
    ℕ → Fin (2^(treeHeight learner a.lambda)) → ℕ :=
  fun t i => GeneralPaperCatalogueGlobalHistory.increment learner shared a k t j i.val

theorem node_levels {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epochIndex : ℕ) (he : epochIndex≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (j : Fin m)
    (i : Fin (2^(treeHeight learner a.lambda))) :
    levelAt (node learner (treesAt (prepare a k Qv weights Bc Br) a k epochIndex) j) i.val=
      GeneralPaperGeometricLevels.levels (history learner (prepare a k Qv weights Bc Br) a k j)
        (epochIndex*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) i := by
  rw [GeneralPaperGeometricLevels.levels_sum]
  exact tree_levels learner a k Qv weights Bc Br epochIndex he j i.val i.isLt

theorem node_mass {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epochIndex : ℕ) (he : epochIndex≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (j : Fin m) :
    GeneralPaperIntervalMass.globalMass (GeneralPaperCachedMassJoin.base k)
      (node learner (treesAt (prepare a k Qv weights Bc Br) a k epochIndex) j)=
      ∑ i : Fin (2^(treeHeight learner a.lambda)), GeneralPaperGeometricLevels.weights (GeneralPaperCachedMassJoin.base k)
        (history learner (prepare a k Qv weights Bc Br) a k j) (epochIndex*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) i := by
  rw [← GeneralPaperIntervalMass.global_mass_sum,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  unfold GeneralPaperGeometricLevels.weights
  rw [node_levels learner a k Qv weights Bc Br epochIndex he j i]

theorem node_law {m : ℕ} (learner : Learner) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (epochIndex : ℕ) (he : epochIndex≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (j : Fin m)
    (i : Fin (2^(treeHeight learner a.lambda))) :
    GeneralPaperTreeLaw.law k (node learner (treesAt (prepare a k Qv weights Bc Br) a k epochIndex) j) i.val=
      GeneralPaperGeometricLevels.probability (GeneralPaperCachedMassJoin.base k)
        (history learner (prepare a k Qv weights Bc Br) a k j) (epochIndex*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) i := by
  rw [GeneralPaperEpochLaw.probability_ratio]
  unfold GeneralPaperTreeLaw.law
  rw [node_levels learner a k Qv weights Bc Br epochIndex he j i,node_mass learner a k Qv weights Bc Br epochIndex he j]
  simp only [Rat.cast_sum,GeneralPaperGeometricLevels.weights,Rat.cast_pow]

end Blotto.GeneralPaperCatalogueGlobalLaw
