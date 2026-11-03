import Blotto.GeneralPaperCatalogueLossBounds

/-! Both actual native selectors lose at most eta/2 in the rounded signed
tail objective on their own positive coherent pre-update snapshots. Every
valid symbolically feasible literal row is a comparator. Source CDF errors
will subsequently convert this rounded objective to the full learner score.
-/
namespace Blotto.GeneralPaperCatalogueSnapshotScore
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperResponseTag
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRows GeneralPaperCatalogueEpochRun
open GeneralPaperCatalogueOccurrenceHistory GeneralPaperCatalogueEpochMetadata
open GeneralPaperCatalogueOptimizer GeneralPaperCatalogueRowSemantics GeneralPaperEpochSnapshot
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

theorem block_score {m k : ℕ} (ready : Ready m k) (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (blocks : FixedArrayTable m (Block k))
    (hPositive : ∀ j, (blocks.read j).Positive) (hCoherent : ∀ j, (blocks.read j).Coherent)
    (hMono : ∀ j, Monotone (ready.summaries.read j).read)
    (hCodes : ∀ j r, (ready.summaries.read j).read r<2*(8*ready.alphabet.C))
    (B : ℚ) (codes : FixedArrayTable m ℕ) (choices : FixedArrayTable m Choice)
    (hDecode : ∀ j, (decode ready.alphabet ready.response (codes.read j)).choice=some (choices.read j))
    (hBudget : (∑ j, (choices.read j).tag)≤budget B) :
    let prefixes := FixedArrayTable.ofFn (fun j => (blocks.read j).cdf)
    let output := pickRow ready (GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
      (GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows weights prefixes B
    referenceScore k (8*ready.alphabet.C) Qv weights ready.summaries prefixes codes-
      referenceScore k (8*ready.alphabet.C) Qv weights ready.summaries prefixes (rowCodes ready.data output)≤
        (GeneralPaperSourceParameters.prepare k).eta/2 := by
  let values := FixedArrayTable.ofFn (fun j => (blocks.read j).values)
  have hTotal : ∀ j, 0<∑ r, (values.read j).read r := by
    intro j
    simpa only [values,FixedArrayTable.read_ofFn,Block.Positive] using hPositive j
  have hPrefixes : FixedArrayTable.ofFn (fun j => GeneralPaperEpochPrefixArray.build (values.read j))=
      FixedArrayTable.ofFn (fun j => (blocks.read j).cdf) := by
    apply PRGExactRealRAMContract.table_ext
    intro j
    simp only [values,FixedArrayTable.read_ofFn]
    exact (hCoherent j).symm
  obtain ⟨output,hSome,_,hScore⟩ := GeneralPaperCatalogueOptimizerScore.call_guarantee ready Qv hQv weights hWeights values hTotal
    hMono hCodes B codes choices hDecode hBudget
  rw [hPrefixes] at hSome hScore
  dsimp only
  rw [pickRow_eq ready _ _ weights _ B output hSome]
  exact hScore

theorem candidate_score {m k : ℕ} (cache : Cache m k) (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (hOrdered : Ordered cache) (hCodes : CodesValid cache)
    (before : FixedArrayTable m (Snapshot k)) (hPositive : ∀ j, Positive (before.read j))
    (hCoherent : ∀ j, Coherent (before.read j)) (Bc Br : ℚ)
    (codes : FixedArrayTable m ℕ) (choices : FixedArrayTable m Choice)
    (hDecode : ∀ j, (decode cache.alphabet false (codes.read j)).choice=some (choices.read j))
    (hBudget : (∑ j, (choices.read j).tag)≤budget Bc) :
    let rows := chooseRows cache (GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv)
      (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows weights before Bc Br
    let prefixes := FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)
    referenceScore k (8*cache.alphabet.C) Qv weights cache.lambda prefixes codes-
      referenceScore k (8*cache.alphabet.C) Qv weights cache.lambda prefixes (rowCodes cache.candidate.data rows.candidate)≤
        (GeneralPaperSourceParameters.prepare k).eta/2 := by
  have ha : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  have hr : cache.candidate.response=false := by rw [cache.candidate_spec]; rfl
  have hs : cache.candidate.summaries=cache.lambda := by rw [cache.candidate_spec]; rfl
  have he := block_score cache.candidate Qv hQv weights hWeights (FixedArrayTable.ofFn (fun j => (before.read j).lambda))
    (fun j => by rw [FixedArrayTable.read_ofFn]; exact (hPositive j).2.2.1)
    (fun j => by rw [FixedArrayTable.read_ofFn]; exact (hCoherent j).2.2.1)
    (by rw [hs]; exact hOrdered .lambda) (by rw [hs,ha]; exact hCodes .lambda) Bc codes choices
    (by rw [ha,hr]; exact hDecode) hBudget
  rw [ha,hs] at he
  simpa only [chooseRows,FixedArrayTable.read_ofFn] using he

theorem response_score {m k : ℕ} (cache : Cache m k) (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (hOrdered : Ordered cache) (hCodes : CodesValid cache)
    (before : FixedArrayTable m (Snapshot k)) (hPositive : ∀ j, Positive (before.read j))
    (hCoherent : ∀ j, Coherent (before.read j)) (Bc Br : ℚ)
    (codes : FixedArrayTable m ℕ) (choices : FixedArrayTable m Choice)
    (hDecode : ∀ j, (decode cache.alphabet true (codes.read j)).choice=some (choices.read j))
    (hBudget : (∑ j, (choices.read j).tag)≤budget Br) :
    let rows := chooseRows cache (GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv)
      (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows weights before Bc Br
    let prefixes := FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf)
    referenceScore k (8*cache.alphabet.C) Qv weights cache.mu prefixes codes-
      referenceScore k (8*cache.alphabet.C) Qv weights cache.mu prefixes (rowCodes cache.response.data rows.response)≤
        (GeneralPaperSourceParameters.prepare k).eta/2 := by
  have ha : cache.response.alphabet=cache.alphabet := by rw [cache.response_spec]; rfl
  have hr : cache.response.response=true := by rw [cache.response_spec]; rfl
  have hs : cache.response.summaries=cache.mu := by rw [cache.response_spec]; rfl
  have he := block_score cache.response Qv hQv weights hWeights (FixedArrayTable.ofFn (fun j => (before.read j).mu))
    (fun j => by rw [FixedArrayTable.read_ofFn]; exact (hPositive j).2.2.2)
    (fun j => by rw [FixedArrayTable.read_ofFn]; exact (hCoherent j).2.2.2)
    (by rw [hs]; exact hOrdered .mu) (by rw [hs,ha]; exact hCodes .mu) Br codes choices
    (by rw [ha,hr]; exact hDecode) hBudget
  rw [ha,hs] at he
  simpa only [chooseRows,FixedArrayTable.read_ofFn] using he

theorem executed_candidate_score {m k : ℕ} (cache : Cache m k) (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (hOrdered : Ordered cache) (hCodes : CodesValid cache) (Bc Br : ℚ)
    (time : ℕ) (hTime : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (codes : FixedArrayTable m ℕ) (choices : FixedArrayTable m Choice)
    (hDecode : ∀ j, (decode cache.alphabet false (codes.read j)).choice=some (choices.read j))
    (hBudget : (∑ j, (choices.read j).tag)≤budget Bc) :
    let run := selected cache Qv weights Bc Br
    let prefixes := FixedArrayTable.ofFn (fun j => (snapshotAt run time j).lambda.cdf)
    referenceScore k (8*cache.alphabet.C) Qv weights cache.lambda prefixes codes-
      referenceScore k (8*cache.alphabet.C) Qv weights cache.lambda prefixes
        (rowCodes cache.candidate.data (rowsAt run time).candidate)≤(GeneralPaperSourceParameters.prepare k).eta/2 := by
  exact candidate_score cache Qv hQv weights hWeights hOrdered hCodes (beforeAt (selected cache Qv weights Bc Br) time)
    (selected_positive cache Qv weights Bc Br time hTime) (snapshot_coherent _ time) Bc Br codes choices hDecode hBudget

theorem executed_response_score {m k : ℕ} (cache : Cache m k) (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (hOrdered : Ordered cache) (hCodes : CodesValid cache) (Bc Br : ℚ)
    (time : ℕ) (hTime : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (codes : FixedArrayTable m ℕ) (choices : FixedArrayTable m Choice)
    (hDecode : ∀ j, (decode cache.alphabet true (codes.read j)).choice=some (choices.read j))
    (hBudget : (∑ j, (choices.read j).tag)≤budget Br) :
    let run := selected cache Qv weights Bc Br
    let prefixes := FixedArrayTable.ofFn (fun j => (snapshotAt run time j).mu.cdf)
    referenceScore k (8*cache.alphabet.C) Qv weights cache.mu prefixes codes-
      referenceScore k (8*cache.alphabet.C) Qv weights cache.mu prefixes
        (rowCodes cache.response.data (rowsAt run time).response)≤(GeneralPaperSourceParameters.prepare k).eta/2 := by
  exact response_score cache Qv hQv weights hWeights hOrdered hCodes (beforeAt (selected cache Qv weights Bc Br) time)
    (selected_positive cache Qv weights Bc Br time hTime) (snapshot_coherent _ time) Bc Br codes choices hDecode hBudget

end Blotto.GeneralPaperCatalogueSnapshotScore
