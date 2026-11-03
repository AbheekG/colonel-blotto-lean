import Blotto.GeneralPaperFourSummaryArrays

/-! Actual retained epoch forests supply all four families' validity/path
premises. The native cache consumer retains code ordering and initial CDF
closeness. Only summary generation is priced here; the rest of cache
preparation and subsequent optimizer/source execution remain required.
-/
namespace Blotto.GeneralPaperActualSummaryArrays
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem epoch_work {m : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
    (GeneralPaperFourSummaryArrays.run true (fun w => w) primitive W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).2≤
      GeneralPaperFourSummaryArrays.profile primitive W m a.lambda k Qv := by
  exact GeneralPaperFourSummaryArrays.bit_work primitive hMono W m k Qv a c hc _ rfl _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he)

theorem epoch_cache_data {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run bits index primitive W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu=
      cache (prepare a k Qv weights Bc Br) a k trees := by
  dsimp only
  rw [GeneralPaperFourSummaryArrays.epoch_cache_data bits index primitive W m k Qv a c hc _ _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he),hc]
  rfl

theorem ordered {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run bits index primitive W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    GeneralPaperCatalogueEpochMetadata.Ordered (GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu) := by
  dsimp only
  rw [epoch_cache_data bits index primitive W k Qv a c hc weights Bc Br epoch he]
  exact GeneralPaperCatalogueTreeCache.ordered a k _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he)

theorem initial_close {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) (field : Fin m) :
    let trees := treesAt (prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run bits index primitive W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let returned := GeneralPaperCatalogueEpochCache.prepare a k arrays.p arrays.q arrays.lambda arrays.mu
    GeneralPaperCDFReweighting.CDFClose (GeneralPaperTreeLaw.law k (node learner trees field))
      (GeneralPaperSummaryOccurrences.uniform (GeneralPaperCatalogueOccurrenceHistory.summary learner returned field).read)
      (GeneralPaperCatalogueEpochMetadata.width learner returned-1) ((GeneralPaperSourceParameters.prepare k).nu:ℝ) := by
  dsimp only
  rw [epoch_cache_data bits index primitive W k Qv a c hc weights Bc Br epoch he]
  exact GeneralPaperCatalogueTreeCache.initial_close a k _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he) learner field

theorem returned_cache {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    ready.2.source=GeneralPaperMaterializedPowerCache.specification m ready.1.1.1.2.lambda k Qv := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  rfl

theorem from_shared_work {m : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hShared : shared=prepare a k Qv weights Bc Br) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let trees := treesAt shared a k epoch
    (GeneralPaperFourSummaryArrays.run true (fun w => w) primitive W m k Qv a c hc shared.wordWidth trees).2≤
      GeneralPaperFourSummaryArrays.profile primitive W m a.lambda k Qv := by
  subst shared
  exact epoch_work primitive hMono W k Qv a c hc weights Bc Br epoch he

theorem prepared_epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let trees := treesAt ready.1.2 a k epoch
    (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a ready.2.source
      (returned_cache model k Qv b weights Bc Br) ready.1.2.wordWidth trees).2≤
      GeneralPaperFourSummaryArrays.profile model.rat W m a.lambda k Qv := by
  let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
  have hShared : ready.1.2=prepare ready.1.1.1.2 k Qv weights Bc Br := by
    dsimp only [ready]
    rw [GeneralPaperPreparedSharedSource.data]
  have hEpoch : epoch≤(GeneralPaperTrajectoryParameters.prepare ready.1.1.1.2.lambda k).epochs := by
    simpa only [ready,GeneralPaperPreparedSharedSource.data] using he
  exact from_shared_work model.rat model.monotone W k Qv ready.1.1.1.2 ready.2.source
    (returned_cache model k Qv b weights Bc Br) ready.1.2 weights Bc Br hShared epoch hEpoch

theorem returned_arithmetic_cache {m : ℕ} (k Qv : ℕ) (b : ℝ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    let ready := (GeneralPaperPreparedSharedSource.arithmetic k Qv b weights Bc Br).1
    ready.2.source=GeneralPaperMaterializedPowerCache.specification m ready.1.1.1.2.lambda k Qv := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.arithmetic_data]
  rfl

theorem prepared_arithmetic_work {m : ℕ} (k Qv : ℕ) (b : ℝ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) :
    let ready := (GeneralPaperPreparedSharedSource.arithmetic k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let trees := treesAt ready.1.2 a k epoch
    (GeneralPaperFourSummaryArrays.run false (fun _ => 1) (fun _ => 1) 1 m k Qv a ready.2.source
      (returned_arithmetic_cache k Qv b weights Bc Br) ready.1.2.wordWidth trees).2≤
      GeneralPaperFourSummaryArrays.arithmeticProfile m a.lambda k Qv := by
  let ready := (GeneralPaperPreparedSharedSource.arithmetic k Qv b weights Bc Br).1
  have hShared : ready.1.2=prepare ready.1.1.1.2 k Qv weights Bc Br := by
    dsimp only [ready]
    rw [GeneralPaperPreparedSharedSource.arithmetic_data]
  have hDigits : ready.1.2.wordWidth=GeneralPaperQuantileComparison.width ready.1.1.1.2.lambda k := by rw [hShared]; rfl
  exact GeneralPaperFourSummaryArrays.arithmetic_work m k Qv ready.1.1.1.2 ready.2.source
    (returned_arithmetic_cache k Qv b weights Bc Br) ready.1.2.wordWidth hDigits _

theorem prepared_same_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let trees := treesAt ready.1.2 a k epoch
    (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a ready.2.source
      (returned_cache model k Qv b weights Bc Br) ready.1.2.wordWidth trees).1=
      (GeneralPaperFourSummaryArrays.run false (fun _ => 1) (fun _ => 1) 1 m k Qv a ready.2.source
        (returned_cache model k Qv b weights Bc Br) ready.1.2.wordWidth trees).1 := by
  let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
  have hShared : ready.1.2=prepare ready.1.1.1.2 k Qv weights Bc Br := by
    dsimp only [ready]
    rw [GeneralPaperPreparedSharedSource.data]
  have hEpoch : epoch≤(GeneralPaperTrajectoryParameters.prepare ready.1.1.1.2.lambda k).epochs := by
    simpa only [ready,GeneralPaperPreparedSharedSource.data] using he
  have hv : Valid ready.1.1.1.2 k (treesAt ready.1.2 ready.1.1.1.2 k epoch) := by
    rw [hShared]
    exact GeneralPaperCatalogueOuterValidity.trees_valid _ _ _ weights Bc Br epoch hEpoch
  have hp : Paths ready.1.1.1.2 k (treesAt ready.1.2 ready.1.1.1.2 k epoch) := by
    rw [hShared]
    exact GeneralPaperCatalogueOuterValidity.trees_paths _ _ _ weights Bc Br epoch hEpoch
  exact GeneralPaperFourSummaryArrays.same_data model.rat W m k Qv ready.1.1.1.2 ready.2.source
    (returned_cache model k Qv b weights Bc Br) ready.1.2.wordWidth _ hv hp

end Blotto.GeneralPaperActualSummaryArrays
