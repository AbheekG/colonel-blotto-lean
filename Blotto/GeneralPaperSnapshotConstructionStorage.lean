import Blotto.GeneralPaperEpochNumeratorConstructionStorage

/-! Complete native four-block snapshot construction. Numerator/prefix
handoffs retain the actual returned numerator array. Full block and snapshot
returns coexist with input fields, constructor buffers, frames and controls.
All prefix total/word caps derive from the actual numerator construction. -/
namespace Blotto.GeneralPaperSnapshotConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEpochFieldState GeneralPaperEpochSnapshot
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

theorem prefix_bound (model : RationalCostModel) (W m lambda k Qv used copied : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (levels : Summary k)
    (hl : ∀ r,levels.read r≤c.controls.precision.levelBound) :
    GeneralPaperEpochPrefixConstructionStorage.window model W used copied
      (GeneralPaperEpochNumeratorArrayPrice.run true (fun w => w) model.rat W c levels).1≤
      GeneralPaperEpochPrefixConstructionStorage.shortProfile model W
        (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) (GeneralPaperSourceParameters.prepare k).summarySize := by
  let nums := (GeneralPaperEpochNumeratorArrayPrice.run true (fun w => w) model.rat W c levels).1
  let cap := (GeneralPaperSourceParameters.prepare k).summarySize*(4*c.powers.format.unit)
  have ht := GeneralPaperEpochNumeratorEnvelope.returned_total true (fun w => w) model.rat W m lambda k Qv c hc levels hl
  have hw : natBits cap≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    dsimp only [cap]
    rw [hc]
    exact GeneralPaperEpochNumeratorEnvelope.total_word m lambda k Qv
  have hs : 1≤(GeneralPaperSourceParameters.prepare k).summarySize := by
    rw [(GeneralPaperSourceParameters.data k).2.2.2.2.2]
    exact Nat.two_pow_pos _
  have hcap : 4*c.powers.format.unit≤cap := by
    have h := Nat.mul_le_mul_right (4*c.powers.format.unit) hs
    simpa only [Nat.one_mul] using h
  have hv : ∀ r,nums.read r≤cap := fun r =>
    (GeneralPaperEpochNumeratorArrayPrice.returned_bound true (fun w => w) model.rat W m lambda k Qv c hc levels hl r).trans hcap
  exact (GeneralPaperEpochPrefixConstructionStorage.bounded model W cap _ used copied nums hv ht hw).trans
    (GeneralPaperEpochPrefixConstructionStorage.profile_short model W cap _ _ hw)

theorem block_returned (model : RationalCostModel) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (levels : Summary k)
    (hl : ∀ r,levels.read r≤c.controls.precision.levelBound) :
    GeneralPaperEncodedSnapshotStorage.blockFootprint W (GeneralPaperEpochSnapshotPrice.block true (fun w => w) model.rat W c levels).1≤
      GeneralPaperEncodedSnapshotStorage.blockProfile W m lambda k Qv := by
  let nums := (GeneralPaperEpochNumeratorArrayPrice.run true (fun w => w) model.rat W c levels).1
  let cap := (GeneralPaperSourceParameters.prepare k).summarySize*(4*c.powers.format.unit)
  have ht := GeneralPaperEpochNumeratorEnvelope.returned_total true (fun w => w) model.rat W m lambda k Qv c hc levels hl
  have hw : natBits cap≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    dsimp only [cap]
    rw [hc]
    exact GeneralPaperEpochNumeratorEnvelope.total_word m lambda k Qv
  have hn := GeneralPaperEncodedNatArray.bounded W (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) nums (by
    intro r
    have h := GeneralPaperEpochNumeratorArrayPrice.returned_bound true (fun w => w) model.rat W m lambda k Qv c hc levels hl r
    have hu : c.powers.format.unit=(GeneralPaperPowerPrecision.prepare lambda k).unit := by rw [hc]; rfl
    rw [hu] at h
    exact GeneralPaperEncodedSnapshotStorage.numerator_word m lambda k Qv _ h)
  have hp := GeneralPaperEpochPrefixConstructionStorage.returned_bound model W cap _ nums ht hw
  change GeneralPaperEncodedNatArray.footprint W nums+
    GeneralPaperEncodedNatArray.footprint W (GeneralPaperEpochPrefixPrice.run true (fun w => w) model.rat W nums).1+32*W≤_
  unfold GeneralPaperEncodedSnapshotStorage.blockProfile
  nlinarith only [hn,hp]

def blockWindow (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    {k : ℕ} (levels : Summary k) (count used copied : ℕ) (ht : count≤(GeneralPaperSourceParameters.prepare k).summarySize) : ℕ :=
  GeneralPaperEpochNumeratorConstructionStorage.window model W c levels count ht+
    GeneralPaperEpochPrefixConstructionStorage.window model W used copied
      (GeneralPaperEpochNumeratorArrayPrice.run true (fun w => w) model.rat W c levels).1+
    GeneralPaperEncodedSnapshotStorage.blockFootprint W (GeneralPaperEpochSnapshotPrice.block true (fun w => w) model.rat W c levels).1+
    fields W [count,(GeneralPaperSourceParameters.prepare k).summarySize,
      (GeneralPaperSourceParameters.prepare k).summarySize+1,(GeneralPaperSourceParameters.prepare k).summarySize+2]+256*W

def blockProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let S := (GeneralPaperSourceParameters.prepare k).summarySize
  GeneralPaperEpochNumeratorConstructionStorage.profile model W m lambda k Qv S+
    GeneralPaperEpochPrefixConstructionStorage.shortProfile model W (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) S+
    GeneralPaperEncodedSnapshotStorage.blockProfile W m lambda k Qv+4*(natBits (S+2)+W)+288*W

theorem block_bound (model : RationalCostModel) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (levels : Summary k)
    (hl : ∀ r,levels.read r≤c.controls.precision.levelBound) (count used copied : ℕ)
    (ht : count≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    blockWindow model W c levels count used copied ht≤blockProfile model W m lambda k Qv := by
  have hn := GeneralPaperEpochNumeratorConstructionStorage.bounded model W m lambda k Qv c hc levels hl count ht
  have hp := prefix_bound model W m lambda k Qv used copied c hc levels hl
  have hr := block_returned model W m lambda k Qv c hc levels hl
  have hf := fields_bound W (natBits ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    [count,(GeneralPaperSourceParameters.prepare k).summarySize,(GeneralPaperSourceParameters.prepare k).summarySize+1,
      (GeneralPaperSourceParameters.prepare k).summarySize+2] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with hx|hx|hx|hx <;> rw [hx] <;>
        exact Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1)
  change _≤4*(natBits ((GeneralPaperSourceParameters.prepare k).summarySize+2)+W)+32*W at hf
  dsimp only [blockWindow,blockProfile]
  omega

def fieldWindow {k : ℕ} (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (state : State k) (count used copied : ℕ) (ht : count≤(GeneralPaperSourceParameters.prepare k).summarySize) : ℕ :=
  blockWindow model W c state.pOccurrences count used copied ht+blockWindow model W c state.qOccurrences count used copied ht+
    blockWindow model W c state.lambdaOccurrences count used copied ht+blockWindow model W c state.muOccurrences count used copied ht+
    GeneralPaperEncodedEpochLevels.fieldFootprint W state+
    GeneralPaperEncodedSnapshotStorage.fieldFootprint W (GeneralPaperEpochSnapshotPrice.take true (fun w => w) model.rat W c state).1+
    fields W [count,(GeneralPaperSourceParameters.prepare k).summarySize,4]+256*W

def fieldProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  4*blockProfile model W m lambda k Qv+GeneralPaperEncodedEpochLevels.fieldProfile W m lambda k Qv+
    GeneralPaperEncodedSnapshotStorage.fieldProfile W m lambda k Qv+
    3*(natBits ((GeneralPaperSourceParameters.prepare k).summarySize+4)+W)+288*W

theorem field_returned {k : ℕ} (model : RationalCostModel) (W m lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (state : State k)
    (hb : Bounded state c.controls.precision.levelBound) :
    GeneralPaperEncodedSnapshotStorage.fieldFootprint W (GeneralPaperEpochSnapshotPrice.take true (fun w => w) model.rat W c state).1≤
      GeneralPaperEncodedSnapshotStorage.fieldProfile W m lambda k Qv := by
  have hp := block_returned model W m lambda k Qv c hc state.pOccurrences hb.1
  have hq := block_returned model W m lambda k Qv c hc state.qOccurrences hb.2.1
  have hl := block_returned model W m lambda k Qv c hc state.lambdaOccurrences hb.2.2.1
  have hu := block_returned model W m lambda k Qv c hc state.muOccurrences hb.2.2.2.1
  dsimp only [GeneralPaperEpochSnapshotPrice.take,GeneralPaperEncodedSnapshotStorage.fieldFootprint,
    GeneralPaperEncodedSnapshotStorage.fieldProfile]
  omega

theorem field_bound {k : ℕ} (model : RationalCostModel) (W m lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (state : State k)
    (hb : Bounded state c.controls.precision.levelBound) (hn : GeneralPaperEncodedEpochLevels.Counts state)
    (count used copied : ℕ) (ht : count≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    fieldWindow model W c state count used copied ht≤fieldProfile model W m lambda k Qv := by
  have hp := block_bound model W m lambda k Qv c hc state.pOccurrences hb.1 count used copied ht
  have hq := block_bound model W m lambda k Qv c hc state.qOccurrences hb.2.1 count used copied ht
  have hl := block_bound model W m lambda k Qv c hc state.lambdaOccurrences hb.2.2.1 count used copied ht
  have hu := block_bound model W m lambda k Qv c hc state.muOccurrences hb.2.2.2.1 count used copied ht
  have hG : c.controls.precision.levelBound=GeneralPaperPowerPrecision.levelBound lambda k := by rw [hc]; rfl
  have hb' := hb
  rw [hG] at hb'
  have hi := GeneralPaperEncodedEpochLevels.field_bound W m lambda Qv state hn hb'
  have hr := field_returned model W m lambda Qv c hc state hb
  have hf := fields_bound W (natBits ((GeneralPaperSourceParameters.prepare k).summarySize+4))
    [count,(GeneralPaperSourceParameters.prepare k).summarySize,4] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with hx|hx|hx <;> rw [hx] <;>
        exact Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1)
  change _≤3*(natBits ((GeneralPaperSourceParameters.prepare k).summarySize+4)+W)+32*W at hf
  dsimp only [fieldWindow,fieldProfile]
  omega

end Blotto.GeneralPaperSnapshotConstructionStorage
