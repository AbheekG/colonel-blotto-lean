import Blotto.GeneralPaperCatalogueEpochCDF

/-! Discharge initial probability, summary ordering, code and CDF-certificate
assumptions with the actual incoming sparse trees and quantile construction.
The true within-epoch CDF reweights those incoming laws by the executed local
increments. Deriving the incoming trees from the preceding outer epoch is
the remaining recurrence join, rather than a supplied initial CDF oracle.
-/
namespace Blotto.GeneralPaperCatalogueTreeCDF
open GeneralPaperCodeAlphabet GeneralPaperCatalogueOccurrenceHistory GeneralPaperCatalogueEpochRun
open GeneralPaperCatalogueTreeCache
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

theorem raw_error {m : ℕ} (a : Alphabet) (k : ℕ) (trees : Trees m a.lambda)
    (hValid : Valid a k trees) (hPaths : Paths a k trees) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (learner : Learner) (j : Fin m) (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (cut : ℕ) (hCut : cut≤2^(treeHeight learner a.lambda)) :
    let cache := prepare (GeneralPaperPreparedPowers.prepare a.lambda k) (GeneralPaperQuantileComparison.width a.lambda k) a k trees
    |GeneralPaperCatalogueEpochCDF.currentCDF learner cache Qv weights Bc Br (GeneralPaperTreeLaw.law k (node learner trees j)) count j cut-
      GeneralPaperRawEpochCDF.raw k (summary learner cache j)
        (block learner (snapshotAt (selected cache Qv weights Bc Br) count j)).cdf cut|<
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ) := by
  let cache := prepare (GeneralPaperPreparedPowers.prepare a.lambda k) (GeneralPaperQuantileComparison.width a.lambda k) a k trees
  have hp : GeneralPaperCDFReweighting.ProbabilityOn (GeneralPaperTreeLaw.law k (node learner trees j))
      (GeneralPaperCatalogueEpochMetadata.width learner cache-1) := by
    rw [width_node]
    exact GeneralPaperTreeLaw.probability_on k _
  exact GeneralPaperCatalogueEpochCDF.raw_error learner cache Qv weights Bc Br (ordered a k trees hValid hPaths)
    (codes_valid _ _ a k trees) j _ hp (initial_close a k trees hValid hPaths learner j) count hCount cut
    (by rw [width_node]; exact hCut)

end Blotto.GeneralPaperCatalogueTreeCDF
