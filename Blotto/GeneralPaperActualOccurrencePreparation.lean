import Blotto.GeneralPaperQueryLossPrice

/-! Actual generated four-family code bounds supply every occurrence-plan
preparation premise. Candidate/response modes use opposite unsigned CDFs,
own unsigned occurrences and the same retained signed learner as native.
-/
namespace Blotto.GeneralPaperActualOccurrencePreparation
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOptionPlans (signed)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem four_codes (bits : Bool) (index price : ℕ → ℕ) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hArrays : arrays=(GeneralPaperFourSummaryArrays.run bits index price W m k Qv a c hc digits trees).1) :
    (∀ j r,(arrays.p.read j).read r<8*a.C) ∧ (∀ j r,(arrays.q.read j).read r<8*a.C) ∧
    (∀ j r,(arrays.lambda.read j).read r<2*(8*a.C)) ∧ (∀ j r,(arrays.mu.read j).read r<2*(8*a.C)) := by
  have h := GeneralPaperSourceRankCache.codes bits index price W m k Qv a c hc digits trees hValid hPaths
  dsimp only at h
  rw [←hArrays] at h
  exact ⟨h .p,h .q,h .lambda,h .mu⟩

theorem generated_work (bits : Bool) (index price : ℕ → ℕ) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hArrays : arrays=(GeneralPaperFourSummaryArrays.run bits index price W m k Qv a c hc digits trees).1)
    (model : RationalCostModel) (response : Bool) (j : Fin m) :
    let own := (if response then arrays.q else arrays.p).read j
    let opposite := (if response then arrays.p else arrays.q).read j
    let signedSummary := (signed response arrays).read j
    (GeneralPaperQueryLossExecution.run true (fun w => w) model.rat W k (8*a.C) opposite signedSummary own).2≤
      GeneralPaperQueryLossPrice.profile model.rat W (GeneralPaperSourceParameters.prepare k).summarySize k (8*a.C) ∧
    (GeneralPaperSignedUpdateExecution.run true (fun w => w) model.rat W k (8*a.C) own signedSummary).2≤
      GeneralPaperSignedUpdatePrice.profile model.rat W (GeneralPaperSourceParameters.prepare k).summarySize k (8*a.C) ∧
    (GeneralPaperQueryLossExecution.run false (fun _ => 1) (fun _ => 1) 1 k (8*a.C) opposite signedSummary own).2≤
      GeneralPaperQueryLossPrice.arithmeticProfile (GeneralPaperSourceParameters.prepare k).summarySize k ∧
    (GeneralPaperSignedUpdateExecution.run false (fun _ => 1) (fun _ => 1) 1 k (8*a.C) own signedSummary).2≤
      GeneralPaperSignedUpdatePrice.arithmeticProfile (GeneralPaperSourceParameters.prepare k).summarySize k := by
  have h := four_codes bits index price W m k Qv a c hc digits trees hValid hPaths arrays hArrays
  have hOwn : ∀ r,((if response then arrays.q else arrays.p).read j).read r<8*a.C := by
    cases response
    · exact h.1 j
    · exact h.2.1 j
  have hOther : ∀ r,((if response then arrays.p else arrays.q).read j).read r<8*a.C := by
    cases response
    · exact h.2.1 j
    · exact h.1 j
  have hSigned : ∀ r,((signed response arrays).read j).read r<2*(8*a.C) := by
    cases response
    · exact h.2.2.1 j
    · exact h.2.2.2 j
  exact ⟨GeneralPaperQueryLossPrice.bit_work model.rat model.monotone W k (8*a.C) _ _ _ hOwn (fun r => (hOther r).le) (fun r => (hSigned r).le),
    GeneralPaperSignedUpdatePrice.bit_work model.rat model.monotone W k (8*a.C) _ _ hSigned (fun r => (hOwn r).le),
    GeneralPaperQueryLossPrice.arithmetic_work k (8*a.C) _ _ _,GeneralPaperSignedUpdatePrice.arithmetic_work k (8*a.C) _ _⟩


theorem epoch_cache_occurrences_data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (a : Alphabet) (response : Bool) (arrays : GeneralPaperFourSummaryArrays.Arrays m k) (j : Fin m) :
    let own := (if response then arrays.q else arrays.p).read j
    let opposite := (if response then arrays.p else arrays.q).read j
    let signedSummary := (signed response arrays).read j
    let cache := GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu
    (GeneralPaperQueryLossExecution.run bits index price W k (8*a.C) opposite signedSummary own).1=
      (if response then (cache.plans.read j).qOccurrences else (cache.plans.read j).pOccurrences) ∧
    (GeneralPaperSignedUpdateExecution.run bits index price W k (8*a.C) own signedSummary).1=
      (if response then (cache.plans.read j).muOccurrences else (cache.plans.read j).lambdaOccurrences) := by
  dsimp only
  rw [GeneralPaperQueryLossExecution.data,GeneralPaperSignedUpdateExecution.data]
  cases response <;>
    simp only [signed,Bool.false_eq_true,ite_false,ite_true,GeneralPaperCatalogueEpochCache.plan_read] <;>
    constructor <;> rfl

theorem epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (response : Bool) (j : Fin m) :
    let trees := GeneralPaperCatalogueOuterLoop.treesAt (GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let own := (if response then arrays.q else arrays.p).read j
    let opposite := (if response then arrays.p else arrays.q).read j
    let signedSummary := (signed response arrays).read j
    (GeneralPaperQueryLossExecution.run true (fun w => w) model.rat W k (8*a.C) opposite signedSummary own).2≤
      GeneralPaperQueryLossPrice.profile model.rat W (GeneralPaperSourceParameters.prepare k).summarySize k (8*a.C) ∧
    (GeneralPaperSignedUpdateExecution.run true (fun w => w) model.rat W k (8*a.C) own signedSummary).2≤
      GeneralPaperSignedUpdatePrice.profile model.rat W (GeneralPaperSourceParameters.prepare k).summarySize k (8*a.C) ∧
    (GeneralPaperQueryLossExecution.run false (fun _ => 1) (fun _ => 1) 1 k (8*a.C) opposite signedSummary own).2≤
      GeneralPaperQueryLossPrice.arithmeticProfile (GeneralPaperSourceParameters.prepare k).summarySize k ∧
    (GeneralPaperSignedUpdateExecution.run false (fun _ => 1) (fun _ => 1) 1 k (8*a.C) own signedSummary).2≤
      GeneralPaperSignedUpdatePrice.arithmeticProfile (GeneralPaperSourceParameters.prepare k).summarySize k :=
  generated_work true (fun w => w) model.rat W m k Qv a c hc _ _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he) _ rfl model response j

end Blotto.GeneralPaperActualOccurrencePreparation
