import Blotto.GeneralPaperForestConstructorOperands
import Blotto.GeneralPaperInstructionConstructionStorage

/-! One actual forest callback joins instruction construction, its full
returned list, batch traversal/query scratch, complete returned annotations,
the updated node and caller controls. All premises come from reached final
fields and retained source trees; no list/level validation executes. -/
namespace Blotto.GeneralPaperEpochNodeConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory GeneralPaperIntervalCache GeneralPaperCatalogueCellHistory
open GeneralPaperCatalogueEpochRun
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def instructionWindow {m k : ℕ} {cache : GeneralPaperCatalogueEpochCache.Cache m k} (W : ℕ) (learner : Learner)
    (state : GeneralPaperCatalogueEpochCache.State cache) (j : Fin m) (remaining : ℕ) : ℕ :=
  let n := (partition learner (cache.plans.read j)).count
  let cells := (partition learner (cache.plans.read j)).intervals
  let levels := levelsOfState learner state j
  let entries := batchOfState learner state j
  listFootprint W (GeneralPaperBatchTraversalStorage.instructionBits W)
      (GeneralPaperIndexedListPrice.fill (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W (n+2))
        (GeneralPaperCellInstructionPrice.element W cells levels) (min remaining n) (Nat.min_le_right ..)
        (entries.drop (min remaining n))).1+GeneralPaperInstructionConstructionStorage.frames W n

def instructionProfile (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperBatchCounterPrice.limit k*(2*GeneralPaperDecoderControls.operandWidth lambda+
    GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+66*W)+32*W+
      GeneralPaperInstructionConstructionStorage.frames W (GeneralPaperBatchCounterPrice.limit k)

theorem instructions_bounded {m k : ℕ} {cache : GeneralPaperCatalogueEpochCache.Cache m k} (W Qv : ℕ) (learner : Learner)
    (state : GeneralPaperCatalogueEpochCache.State cache) (j : Fin m) (remaining : ℕ)
    (hb : GeneralPaperEpochFieldState.Bounded (state.fields.read j) (GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k)) :
    instructionWindow W learner state j remaining≤ instructionProfile W m cache.alphabet.lambda k Qv := by
  have h := GeneralPaperInstructionConstructionStorage.actual_prefix true (fun w => w) W Qv learner state j hb
    (min remaining (partition learner (cache.plans.read j)).count) (Nat.min_le_right ..)
  exact h.trans_eq (by dsimp only [instructionProfile]; ring)

theorem list_returned {m k : ℕ} {cache : GeneralPaperCatalogueEpochCache.Cache m k} (W Qv : ℕ) (learner : Learner)
    (state : GeneralPaperCatalogueEpochCache.State cache) (j : Fin m)
    (hb : GeneralPaperEpochFieldState.Bounded (state.fields.read j) (GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k)) :
    listFootprint W (GeneralPaperBatchTraversalStorage.instructionBits W)
      (GeneralPaperActualEpochInstructions.run true (fun w => w) W learner state j).1≤ instructionProfile W m cache.alphabet.lambda k Qv := by
  rw [GeneralPaperActualEpochInstructions.data]
  have hl := GeneralPaperActualEpochInstructions.length true (fun w => w) W learner state j
  rw [GeneralPaperActualEpochInstructions.data] at hl
  have h := GeneralPaperBatchTraversalStorage.list_bound W m cache.alphabet.lambda k Qv (batchOfState learner state j)
    (GeneralPaperActualBatchStorage.good learner state j hb)
  have hp := Nat.mul_le_mul_right
    (2*GeneralPaperDecoderControls.operandWidth cache.alphabet.lambda+GeneralPaperPowerPreparationEnvelope.operandWidth m cache.alphabet.lambda k Qv+66*W) hl
  unfold instructionProfile
  omega

theorem range_profile_mono (model : RationalCostModel) (W m lambda k Qv h H : ℕ) (hh : h≤H) :
    GeneralPaperRangeQueryStorage.profile model W m lambda k Qv h≤GeneralPaperRangeQueryStorage.profile model W m lambda k Qv H := by
  unfold GeneralPaperRangeQueryStorage.profile
  gcongr

def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) (learner : Learner) (j : Fin m) (remaining : ℕ) : ℕ :=
  let shared := prepare a k Qv weights Bc Br
  let trees := treesAt shared a k epoch
  let cache := GeneralPaperCatalogueShared.cache shared a k trees
  let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
  let height := treeHeight learner a.lambda
  let span0 := span learner shared
  let result := GeneralPaperEpochNodeUpdate.run true (fun w => w) model.rat W c learner state j height (node learner trees j) span0
  instructionWindow W learner state j remaining+
    listFootprint W (GeneralPaperBatchTraversalStorage.instructionBits W) (GeneralPaperActualEpochInstructions.run true (fun w => w) W learner state j).1+
    GeneralPaperBatchTraversalStorage.peak model W c height span0 (node learner trees j) (batchOfState learner state j)+
    GeneralPaperBatchTraversalStorage.resultBits W result.1+GeneralPaperSparseNodeBits.footprint W result.1.node+
    fields W [m,j.val,height,(partition learner (cache.plans.read j)).count,(partition learner (cache.plans.read j)).count+1,0,1]+
    rationalWordWidth span0+(GeneralPaperForestUpdateExecution.element true (fun w => w) model.rat W c shared trees state learner j).2+256*W

def profile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let B := GeneralPaperBatchCounterPrice.limit k
  let L := GeneralPaperDecoderControls.operandWidth lambda
  2*instructionProfile W m lambda k Qv+(B+1)*GeneralPaperBatchTraversalStorage.frameProfile model W m lambda k Qv+
    GeneralPaperRangeQueryStorage.profile model W m lambda k Qv (lambda+1)+(8*H+64*W)+
    GeneralPaperForestConstructorOperands.nodeProfile W m lambda k Qv+
    (7*(H+natBits (m+1)+natBits (B+1)+W)+32*W)+L+
    (GeneralPaperEpochNodeUpdate.profile model.rat W m lambda k Qv+2*model.rat H+256*W)+256*W

theorem bounded {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) (j : Fin m) (remaining : ℕ) :
    window model W k Qv a c weights Bc Br epoch learner j remaining≤profile model W m a.lambda k Qv := by
  let shared := prepare a k Qv weights Bc Br
  let trees := treesAt shared a k epoch
  let cache := GeneralPaperCatalogueShared.cache shared a k trees
  let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
  let height := treeHeight learner a.lambda
  let span0 := span learner shared
  let result := GeneralPaperEpochNodeUpdate.run true (fun w => w) model.rat W c learner state j height (node learner trees j) span0
  have hb := selected_cap cache Qv weights Bc Br shared.trajectory.period (Nat.le_refl _) j
  have hi := instructions_bounded W Qv learner state j remaining hb
  have hl := list_returned W Qv learner state j hb
  change instructionWindow W learner state j remaining≤ instructionProfile W m a.lambda k Qv at hi
  change listFootprint W (GeneralPaperBatchTraversalStorage.instructionBits W)
    (GeneralPaperActualEpochInstructions.run true (fun w => w) W learner state j).1≤ instructionProfile W m a.lambda k Qv at hl
  have hbatch := (GeneralPaperActualBatchStorage.epoch model W k Qv a c hc weights Bc Br epoch he learner j).trans
    (Nat.add_le_add_left (range_profile_mono model W m a.lambda k Qv height (a.lambda+1) (tree_height_bound learner a.lambda)) _)
  have hs : span0=(2:ℚ)^height := span_power learner a k Qv weights Bc Br
  have hv := GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch (by omega)
  have hf := GeneralPaperActualForestUpdate.final_cap a k Qv weights Bc Br epoch he
  have hd := GeneralPaperEpochNodeUpdate.data true (fun w => w) model.rat W Qv c hc learner state j height (node learner trees j) span0 hs (hv learner j) (hf learner j)
  have hn := GeneralPaperActualEpochInstructions.length true (fun w => w) W learner state j
  rw [GeneralPaperActualEpochInstructions.data] at hn
  have hpowers : c.powers=GeneralPaperPreparedPowers.prepare a.lambda k := by rw [hc]; rfl
  have hr := GeneralPaperBatchTraversalStorage.result_bound W m a.lambda k Qv height span0 (node learner trees j) (batchOfState learner state j)
    (tree_height_bound learner a.lambda) (by rw [hs]; positivity) hn
  rw [←hpowers,←hd] at hr
  have hnode := GeneralPaperForestConstructorOperands.element_bound model W k Qv a c hc weights Bc Br epoch he learner j
  change GeneralPaperSparseNodeBits.footprint W result.1.node≤_ at hnode
  have hheight := GeneralPaperSparseNodeBits.height_word m a.lambda k Qv height (tree_height_bound learner a.lambda)
  have h0 := GeneralPaperSparseNodeBits.height_word m a.lambda k Qv 0 (by omega)
  have h1 := GeneralPaperSparseNodeBits.height_word m a.lambda k Qv 1 (by omega)
  have hcount := GeneralPaperActualEpochInstructions.cell_count learner cache j
  have hspan := GeneralPaperRangeGeometryPrice.rational_word a.lambda span0
    (GeneralPaperRangeGeometryPrice.window_bounds a.lambda height 0 span0 (by rw [hs]; exact GeneralPaperRangeGeometryPrice.root_window a.lambda height (tree_height_bound learner a.lambda))).2.1
  have hcontrols := fields_bound W (GeneralPaperPowerPreparationEnvelope.operandWidth m a.lambda k Qv+natBits (m+1)+natBits (GeneralPaperBatchCounterPrice.limit k+1))
    [m,j.val,height,(partition learner (cache.plans.read j)).count,(partition learner (cache.plans.read j)).count+1,0,1] (by
      have hm := GeneralPaperRankStorageMonotonicity.nat_word m (m+1) (by omega)
      have hj := GeneralPaperRankStorageMonotonicity.nat_word j.val (m+1) (by have := j.isLt; omega)
      have hn0 := GeneralPaperRankStorageMonotonicity.nat_word (partition learner (cache.plans.read j)).count (GeneralPaperBatchCounterPrice.limit k+1) (by omega)
      have hn1 := GeneralPaperRankStorageMonotonicity.nat_word ((partition learner (cache.plans.read j)).count+1) (GeneralPaperBatchCounterPrice.limit k+1) (by omega)
      change natBits height≤_ at hheight
      change natBits 0≤_ at h0
      change natBits 1≤_ at h1
      intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals omega)
  have hnprice := GeneralPaperEpochNodeUpdate.bit_work model.rat model.monotone W Qv c hc learner state j height
    (node learner trees j) span0 hs (tree_height_bound learner a.lambda) (hv learner j) (hf learner j)
  have hhprice := GeneralPaperForestUpdatePrice.height_work model.rat model.monotone m a.lambda k Qv learner
  have hprice : (GeneralPaperForestUpdateExecution.element true (fun w => w) model.rat W c shared trees state learner j).2≤
      GeneralPaperEpochNodeUpdate.profile model.rat W m a.lambda k Qv+2*model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m a.lambda k Qv)+256*W :=
    Nat.add_le_add_right (Nat.add_le_add hnprice hhprice) _
  simp only [List.length_cons,List.length_nil] at hcontrols
  dsimp only [window,profile]
  dsimp only [result,state,cache,trees,shared,height,span0] at hi hl hbatch hr hnode hcontrols hspan hprice
  omega

end Blotto.GeneralPaperEpochNodeConstructionStorage
