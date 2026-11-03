import Blotto.GeneralPaperCatalogueOptimizer

/-! Actual cached native row selection is within eta/2 of every valid
symbolically feasible literal code row. The finite catalogue comparison
and optimizer success are derived, not supplied. All source parameters and
the cached plans are reused arguments to the executed call.
-/
namespace Blotto.GeneralPaperCatalogueOptimizerScore
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperCatalogueArrays
open GeneralPaperCatalogueRowSemantics GeneralPaperCatalogueOptimizer
open GeneralPaperResponseTag
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

theorem call_guarantee {m k : ℕ} (ready : Ready m k) (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (values : FixedArrayTable m (Summary k))
    (hTotal : ∀ j, 0<∑ r, (values.read j).read r)
    (hMono : ∀ j, Monotone (ready.summaries.read j).read)
    (hCodes : ∀ j r, (ready.summaries.read j).read r<2*(8*ready.alphabet.C))
    (B : ℚ) (codes : FixedArrayTable m ℕ) (choices : FixedArrayTable m Choice)
    (hDecode : ∀ j, (decode ready.alphabet ready.response (codes.read j)).choice=some (choices.read j))
    (hBudget : (∑ j, (choices.read j).tag)≤budget B) :
    ∃ output,
      call ready (GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
        (GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows weights
        (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) B=some output ∧
      (∑ j, ((rowChoices ready.data output).read j).tag)≤budget B ∧
      referenceScore k (8*ready.alphabet.C) Qv weights ready.summaries
        (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) codes-
      referenceScore k (8*ready.alphabet.C) Qv weights ready.summaries
        (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) (rowCodes ready.data output)≤
        (GeneralPaperSourceParameters.prepare k).eta/2 := by
  let prefixes : FixedArrayTable m (Prefix k) := FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))
  obtain ⟨mapped,hResource,hSameScore⟩ := GeneralPaperCatalogueEmbedding.represents ready.alphabet ready.response k
    (GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows Qv weights ready.summaries prefixes
    hMono hCodes codes choices hDecode
  rw [←ready.data_spec] at hResource hSameScore
  obtain ⟨output,hSolve,hCost,hScore⟩ := GeneralPaperNativeRowScore.score_guarantee ready.alphabet.lambda k Qv
    (8*ready.alphabet.C) hQv (by omega) weights hWeights ready.summaries values hTotal ready.data.codes (tags ready.data) B mapped
    (hResource.trans hBudget)
  rw [hSameScore,score_exact k (8*ready.alphabet.C) Qv weights prefixes ready.summaries ready.data output] at hScore
  refine ⟨output,?_,?_,hScore⟩
  · unfold call
    rw [ready.cached_spec]
    exact hSolve
  · rw [←resource_exact k (8*ready.alphabet.C) (GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows
      weights prefixes ready.summaries ready.data output]
    exact hCost

theorem zero_success {m k : ℕ} (ready : Ready m k) (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (values : FixedArrayTable m (Summary k))
    (hTotal : ∀ j, 0<∑ r, (values.read j).read r) (B : ℚ) (hB : 0≤B) :
    ∃ output, call ready (GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
      (GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows weights
      (FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))) B=some output := by
  have hZero : ∀ j, ((tags ready.data).read j).read 0=0 := by
    rw [ready.data_spec]
    exact GeneralPaperCatalogueArrays.zero_tag ready.alphabet ready.response k ready.summaries
  obtain ⟨output,hSolve⟩ := GeneralPaperNativeRowScore.zero_success ready.alphabet.lambda k Qv (8*ready.alphabet.C) hQv
    weights hWeights ready.summaries values hTotal ready.data.codes (tags ready.data) 0 hZero B hB
  refine ⟨output,?_⟩
  unfold call
  rw [ready.cached_spec]
  exact hSolve

end Blotto.GeneralPaperCatalogueOptimizerScore
