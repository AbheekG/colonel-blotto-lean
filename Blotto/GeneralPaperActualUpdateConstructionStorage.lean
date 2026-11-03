import Blotto.GeneralPaperFieldUpdateConstructionStorage

/-! Actual reached field updates join all eight delta/addition fills and
full returned native states. The complete all-field parent includes old/new
families, reserved prefixes, frames, current field, full returned family,
choice/index controls and the common pre-update snapshot. -/
namespace Blotto.GeneralPaperActualUpdateConstructionStorage
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
open GeneralPaperEncodedScalarStorage GeneralPaperCatalogueEpochRun
open GeneralPaperCatalogueOccurrenceHistory (block)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def nativeWindow {k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (state : State k) (snapshot : Snapshot k)
    (choice : Choice state.plan) (count : ℕ) : ℕ :=
  GeneralPaperFieldUpdateConstructionStorage.deltaWindow model W mesh state snapshot choice count+
    GeneralPaperFieldUpdateConstructionStorage.advanceWindow model W state
      (GeneralPaperFieldDeltaExecution.run true (fun w => w) model.rat W mesh state snapshot choice).1 count+256*W

def nativeProfile (model : RationalCostModel) (W m lambda k Qv C R : ℕ) : ℕ :=
  GeneralPaperFieldUpdateConstructionStorage.deltaProfile model W m lambda k Qv C R+
    GeneralPaperFieldUpdateConstructionStorage.advanceProfile model W m lambda k Qv+256*W

theorem native_bounded {k : ℕ} (model : RationalCostModel) (W m lambda Qv mesh : ℕ) (state : State k) (snapshot : Snapshot k)
    (choice : Choice state.plan) (count : ℕ)
    (hmesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hg : ∀ learner,GeneralPaperMeshPrefixInvariant.Good m lambda k Qv (block learner snapshot).cdf)
    (hsafe : GeneralPaperDeltaPlanBounds.PlanSafe lambda state.plan) (hc : GeneralPaperEncodedEpochLevels.Counts state)
    (hs : Bounded state (GeneralPaperPowerPrecision.levelBound lambda k)) (hp : Positive snapshot) (hh : Coherent snapshot) :
    nativeWindow model W mesh state snapshot choice count≤nativeProfile model W m lambda k Qv state.plan.candidateCount state.plan.responseCount :=
  Nat.add_le_add_right (Nat.add_le_add
    (GeneralPaperFieldUpdateConstructionStorage.delta_bounded model W m lambda Qv mesh state snapshot choice count hmesh hg hsafe hc hp hh)
    (GeneralPaperFieldUpdateConstructionStorage.advance_bounded model W m lambda Qv state _ count hc hs
      (GeneralPaperFieldDeltaExecution.returned_bound true (fun w => w) model.rat W mesh state snapshot choice hmesh hp hh))) _

def fieldProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
  nativeProfile model W m lambda k Qv K K

theorem selected {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ)
    (cache : GeneralPaperCatalogueEpochCache.Cache m k) (hCodes : GeneralPaperCatalogueEpochMetadata.CodesValid cache)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) (count : ℕ) :
    let current := GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br
    nativeWindow model W (GeneralPaperSourceParameters.prepare k).meshDenominator
      (fieldAt current time j) (snapshotAt current time j) (choiceAt current time j) count≤
      fieldProfile model W m cache.alphabet.lambda k Qv := by
  let current := GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br
  have hs : GeneralPaperDeltaPlanBounds.PlanSafe cache.alphabet.lambda (fieldAt current time j).plan := by
    rw [field_plan]
    exact GeneralPaperDeltaPlanBounds.actual_plan cache hCodes j
  have h := native_bounded model W m cache.alphabet.lambda Qv _ (fieldAt current time j) (snapshotAt current time j)
    (choiceAt current time j) count rfl
    (fun learner => GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j learner) hs
    (GeneralPaperEncodedEpochLevels.actual_counts cache _ j (field_plan current time j))
    (selected_cap cache Qv weights Bc Br time ht j)
    (selected_positive cache Qv weights Bc Br time ht j) (snapshot_coherent current time j)
  rw [field_plan,GeneralPaperCatalogueEpochCache.candidate_count,GeneralPaperCatalogueEpochCache.response_count] at h
  exact h

def roundWindow {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : GeneralPaperCatalogueEpochCache.Cache m k)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time count : ℕ) (hc : count≤m) (j : Fin m) (innerCount : ℕ) : ℕ :=
  let current := GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br
  GeneralPaperRoundUpdateStorage.window true (fun w => w) model.rat W Qv cache weights Bc Br time count hc j+
    GeneralPaperGridArrayConstructionStorage.frames W m+
    nativeWindow model W (GeneralPaperSourceParameters.prepare k).meshDenominator
      (fieldAt current time j) (snapshotAt current time j) (choiceAt current time j) innerCount+
    GeneralPaperEncodedEpochLevels.familyFootprint W
      (GeneralPaperRoundFieldsExecution.run true (fun w => w) model.rat W (GeneralPaperSourceParameters.prepare k).meshDenominator
        (stateAt current time) (beforeAt current time) (rowsAt current time)).1.fields+
    fields W [m,count,count+1,m+1,j.val]+320*W

def roundProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperRoundUpdateStorage.profile W m lambda k Qv+GeneralPaperGridArrayConstructionStorage.frames W m+
    fieldProfile model W m lambda k Qv+GeneralPaperEncodedEpochLevels.profile W m lambda k Qv+
    (5*(natBits (m+1)+W)+32*W)+320*W

theorem round_selected {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ)
    (cache : GeneralPaperCatalogueEpochCache.Cache m k) (hCodes : GeneralPaperCatalogueEpochMetadata.CodesValid cache)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (count : ℕ) (hc : count≤m) (j : Fin m) (innerCount : ℕ) :
    roundWindow model W Qv cache weights Bc Br time count hc j innerCount≤roundProfile model W m cache.alphabet.lambda k Qv := by
  let current := GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br
  have hp := GeneralPaperRoundUpdateStorage.window_bound true (fun w => w) model.rat W Qv cache weights Bc Br time ht count hc j
  have hf := selected model W Qv cache hCodes weights Bc Br time (by omega) j innerCount
  have hr : GeneralPaperEncodedEpochLevels.familyFootprint W
      (GeneralPaperRoundFieldsExecution.run true (fun w => w) model.rat W (GeneralPaperSourceParameters.prepare k).meshDenominator
        (stateAt current time) (beforeAt current time) (rowsAt current time)).1.fields≤GeneralPaperEncodedEpochLevels.profile W m cache.alphabet.lambda k Qv := by
    have hdata : (GeneralPaperRoundFieldsExecution.run true (fun w => w) model.rat W (GeneralPaperSourceParameters.prepare k).meshDenominator
        (stateAt current time) (beforeAt current time) (rowsAt current time)).1=stateAt current (time+1) :=
      GeneralPaperRoundFieldsPrice.data true (fun w => w) model.rat W Qv cache
        (GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv) rfl weights Bc Br time
    rw [hdata]
    exact GeneralPaperEncodedEpochLevels.selected W Qv cache weights Bc Br (time+1) ht
  have hi := GeneralPaperMeshPairStorage.index_fields W m [m,count,count+1,m+1,j.val] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl
    all_goals (have := j.isLt; omega))
  simp only [List.length_cons,List.length_nil] at hi
  dsimp only [roundWindow,roundProfile]
  dsimp only [current] at hr
  omega

end Blotto.GeneralPaperActualUpdateConstructionStorage
