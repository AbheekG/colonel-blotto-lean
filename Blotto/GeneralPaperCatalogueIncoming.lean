import Blotto.GeneralPaperCatalogueQueryErrors

/-! Analysis-only incoming laws for the four actual learners. The concrete
constructor below obtains every probability and CDF certificate from the
incoming sparse trees and their executed quantile summaries. No incoming-law
or CDF-certificate callback is passed to the runtime row/epoch algorithm.
-/
namespace Blotto.GeneralPaperCatalogueIncoming
open GeneralPaperCodeAlphabet GeneralPaperCatalogueEpochCache GeneralPaperCatalogueOccurrenceHistory GeneralPaperCatalogueEpochMetadata
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

structure Incoming {m k : ℕ} (cache : Cache m k) where
  mass : Learner → Fin m → ℕ → ℝ
  probability : ∀ learner j, GeneralPaperCDFReweighting.ProbabilityOn (mass learner j) (width learner cache-1)
  close : ∀ learner j, GeneralPaperCDFReweighting.CDFClose (mass learner j)
    (GeneralPaperSummaryOccurrences.uniform (summary learner cache j).read) (width learner cache-1)
    ((GeneralPaperSourceParameters.prepare k).nu:ℝ)

noncomputable def fromTrees {m : ℕ} (a : Alphabet) (k : ℕ) (trees : GeneralPaperCatalogueTreeCache.Trees m a.lambda)
    (hValid : GeneralPaperCatalogueTreeCache.Valid a k trees) (hPaths : GeneralPaperCatalogueTreeCache.Paths a k trees) :
    Incoming (GeneralPaperCatalogueTreeCache.prepare (GeneralPaperPreparedPowers.prepare a.lambda k)
      (GeneralPaperQuantileComparison.width a.lambda k) a k trees) :=
  ⟨fun learner j => GeneralPaperTreeLaw.law k (GeneralPaperCatalogueTreeCache.node learner trees j),
    by intro learner j; rw [GeneralPaperCatalogueTreeCache.width_node]; exact GeneralPaperTreeLaw.probability_on k _,
    GeneralPaperCatalogueTreeCache.initial_close a k trees hValid hPaths⟩

end Blotto.GeneralPaperCatalogueIncoming
