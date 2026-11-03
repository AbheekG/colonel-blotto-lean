import Blotto.GeneralPaperRankArrayPrice

/-! Actual generated four-family summaries supply the rank comparand and
ordering bounds. Signed tail cuts retain their endpoint and sign offset.
These are erased interfaces to existing arrays, not cache replay passes.
-/
namespace Blotto.GeneralPaperSourceRankCache
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOccurrenceHistory
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem codes (bits : Bool) (index primitive : ℕ → ℕ) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees) :
    let arrays := (GeneralPaperFourSummaryArrays.run bits index primitive W m k Qv a c hc digits trees).1
    GeneralPaperCatalogueEpochMetadata.CodesValid
      (GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu) := by
  dsimp only
  rw [GeneralPaperFourSummaryArrays.epoch_cache_data bits index primitive W m k Qv a c hc digits trees hValid hPaths]
  exact GeneralPaperCatalogueTreeCache.codes_valid c.powers digits a k trees

theorem rank_work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees)
    (learner : Learner) (field : Fin m) (cuts : FixedArrayTable n ℕ) (hCuts : ∀ q,cuts.read q≤2^(treeHeight learner a.lambda)) :
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) primitive W m k Qv a c hc digits trees).1
    let cache := GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu
    (GeneralPaperRankArrayExecution.prepare true (fun w => w) primitive W k (summary learner cache field) cuts).2≤
      GeneralPaperRankArrayPrice.profile primitive W n k (2^(treeHeight learner a.lambda)) := by
  dsimp only
  apply GeneralPaperRankArrayPrice.bit_work primitive hMono W k _ _ cuts hCuts
  intro r
  have hCodes := codes true (fun w => w) primitive W m k Qv a c hc digits trees hValid hPaths learner field r
  have hWidth : GeneralPaperCatalogueEpochMetadata.width learner
      (GeneralPaperCatalogueEpochCache.prepare a k
        (GeneralPaperFourSummaryArrays.run true (fun w => w) primitive W m k Qv a c hc digits trees).1.p
        (GeneralPaperFourSummaryArrays.run true (fun w => w) primitive W m k Qv a c hc digits trees).1.q
        (GeneralPaperFourSummaryArrays.run true (fun w => w) primitive W m k Qv a c hc digits trees).1.lambda
        (GeneralPaperFourSummaryArrays.run true (fun w => w) primitive W m k Qv a c hc digits trees).1.mu)=
      2^(treeHeight learner a.lambda) := by
    exact GeneralPaperCatalogueEpochMetadata.width_power learner _
  exact hCodes.le.trans_eq hWidth

theorem rank_spec {n : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (hDigits : digits=GeneralPaperQuantileComparison.width a.lambda k)
    (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees)
    (learner : Learner) (field : Fin m) (cuts : FixedArrayTable n ℕ) (q : Fin n)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    let arrays := (GeneralPaperFourSummaryArrays.run bits index primitive W m k Qv a c hc digits trees).1
    let cache := GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu
    (summary learner cache field).read r<cuts.read q ↔
      r.val<((GeneralPaperRankArrayExecution.prepare bits index primitive W k (summary learner cache field) cuts).1.1.read q).val := by
  dsimp only
  apply GeneralPaperRankArrayData.cached_spec
  rw [GeneralPaperFourSummaryArrays.epoch_cache_data bits index primitive W m k Qv a c hc digits trees hValid hPaths,hc,hDigits]
  exact GeneralPaperCatalogueTreeCache.ordered a k trees hValid hPaths learner field

theorem signed_cuts_bound {n : ℕ} (U : ℕ) (negative : Bool) (queries : FixedArrayTable n ℕ)
    (hQueries : ∀ q,queries.read q≤U) (i : Fin (n+1)) :
    (GeneralPaperSignedTailPlan.cutBuild U negative queries).1.read i≤2*U := by
  rw [GeneralPaperSignedTailPlan.cutBuild,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  unfold GeneralPaperSignedTailPlan.cutValue
  by_cases hi : i.val<n
  · rw [dite_eq_left hi]
    have h := hQueries ⟨i.val,hi⟩
    cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  · rw [dite_eq_right hi]
    cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem code_word (height : ℕ) : binaryWordWidth (2^height+1)≤2*height+4 := by
  have h := GeneralPaperNatPowerOperands.power_width 2 height
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (2^height) 1
  have h2 : binaryWordWidth 2=2 := by decide
  have h1 : binaryWordWidth 1=1 := by decide
  rw [h2] at h
  omega

theorem rank_width (n depth height : ℕ) :
    GeneralPaperRankArrayOperands.width n depth (2^height)≤
      512+32*depth+64*height+16*binaryWordWidth (n+1) := by
  have h := code_word height
  unfold GeneralPaperRankArrayOperands.width GeneralPaperRankOperands.width
  omega

theorem epoch_work {n m : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (learner : Learner) (field : Fin m) (cuts : FixedArrayTable n ℕ) (hCuts : ∀ q,cuts.read q≤2^(treeHeight learner a.lambda)) :
    let trees := GeneralPaperCatalogueOuterLoop.treesAt (GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) primitive W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let cache := GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu
    (GeneralPaperRankArrayExecution.prepare true (fun w => w) primitive W k (summary learner cache field) cuts).2≤
      GeneralPaperRankArrayPrice.profile primitive W n k (2^(treeHeight learner a.lambda)) :=
  rank_work primitive hMono W m k Qv a c hc _ _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he) learner field cuts hCuts

theorem epoch_spec {n m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (learner : Learner) (field : Fin m) (cuts : FixedArrayTable n ℕ) (q : Fin n)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    let trees := GeneralPaperCatalogueOuterLoop.treesAt (GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run bits index primitive W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let cache := GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu
    (summary learner cache field).read r<cuts.read q ↔
      r.val<((GeneralPaperRankArrayExecution.prepare bits index primitive W k (summary learner cache field) cuts).1.1.read q).val :=
  rank_spec bits index primitive W m k Qv a c hc _ rfl _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he) learner field cuts q r

end Blotto.GeneralPaperSourceRankCache
