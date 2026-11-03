import Blotto.GeneralPaperActualBatchStorage

/-! The backward native instruction builder owns the completed suffix and
one current instruction. Remaining+suffix.length supplies every prefix size.
Its structural control stack is counted from the retained cell count, with
no length traversal and no allocation of an intermediate index list. -/
namespace Blotto.GeneralPaperInstructionConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperBatchTraversalStorage
open GeneralPaperCatalogueCellHistory GeneralPaperCatalogueOccurrenceHistory
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem fill_bound {n : ℕ} (index : ℕ → ℕ) (A W P remaining : ℕ)
    (callback : Fin n → GeneralPaperIntervalBatch.Instruction × ℕ)
    (hb : ∀ q,instructionBits W (callback q).1≤P) (hc : remaining≤n)
    (suffix : List GeneralPaperIntervalBatch.Instruction) (hlen : remaining+suffix.length=n)
    (hSuffix : ∀ e∈suffix,instructionBits W e≤P) :
    listFootprint W (instructionBits W) (GeneralPaperIndexedListPrice.fill index A callback remaining hc suffix).1≤
      n*(P+2*W)+32*W := by
  have hs : ∀ e∈(GeneralPaperIndexedListPrice.fill index A callback remaining hc suffix).1,instructionBits W e≤P := by
    rw [GeneralPaperIndexedListPrice.fill_data]
    intro e he
    rcases List.mem_append.mp he with he|he
    · obtain ⟨q,hq⟩ := List.mem_ofFn.mp he
      rw [←hq]
      exact hb _
    · exact hSuffix e he
  have h := GeneralPaperEncodedScalarStorage.list_bound W P (instructionBits W) _ hs
  rw [GeneralPaperIndexedListPrice.every_prefix,hlen] at h
  exact h

def frames (W n : ℕ) : ℕ := (n+1)*(4*natBits (n+1)+128*W)

theorem frames_mono (W n N : ℕ) (hn : n≤N) : frames W n≤frames W N := by
  have hw := binaryWordWidth_mono (Nat.add_le_add_right hn 1)
  unfold frames natBits
  exact Nat.mul_le_mul (Nat.add_le_add_right hn 1) (by omega)

theorem actual_prefix {m k : ℕ} {cache : GeneralPaperCatalogueEpochCache.Cache m k}
    (bits : Bool) (index : ℕ → ℕ) (W Qv : ℕ) (learner : Learner)
    (state : GeneralPaperCatalogueEpochCache.State cache) (j : Fin m)
    (hb : GeneralPaperEpochFieldState.Bounded (state.fields.read j) (GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k))
    (remaining : ℕ) (hc : remaining≤(partition learner (cache.plans.read j)).count) :
    let cells := (partition learner (cache.plans.read j)).intervals
    let levels := levelsOfState learner state j
    let entries := batchOfState learner state j
    let callback := GeneralPaperCellInstructionPrice.element W cells levels
    let P := 2*GeneralPaperDecoderControls.operandWidth cache.alphabet.lambda+
      GeneralPaperPowerPreparationEnvelope.operandWidth m cache.alphabet.lambda k Qv+64*W
    listFootprint W (instructionBits W)
        (GeneralPaperIndexedListPrice.fill index
          (if bits then GeneralPaperSummaryArrayExecution.arrayWord W ((partition learner (cache.plans.read j)).count+2) else W)
          callback remaining hc (entries.drop remaining)).1+
      frames W (partition learner (cache.plans.read j)).count≤
    GeneralPaperBatchCounterPrice.limit k*(P+2*W)+32*W+frames W (GeneralPaperBatchCounterPrice.limit k) := by
  dsimp only
  let n := (partition learner (cache.plans.read j)).count
  let entries := batchOfState learner state j
  let callback := GeneralPaperCellInstructionPrice.element W (partition learner (cache.plans.read j)).intervals (levelsOfState learner state j)
  let P := 2*GeneralPaperDecoderControls.operandWidth cache.alphabet.lambda+
    GeneralPaperPowerPreparationEnvelope.operandWidth m cache.alphabet.lambda k Qv+64*W
  have hGood := GeneralPaperActualBatchStorage.good learner state j hb
  have hEntry : ∀ e∈entries,instructionBits W e≤P := fun e he =>
    instruction_bound W m cache.alphabet.lambda k Qv e (hGood e he).1 (hGood e he).2.1 (hGood e he).2.2
  have hCallback : ∀ q,instructionBits W (callback q).1≤P := by
    intro q
    apply hEntry
    change (callback q).1∈List.ofFn _
    exact List.mem_ofFn.mpr ⟨q,rfl⟩
  have hLength : entries.length=n := GeneralPaperEpochCellInstructions.build_length _ _
  have hSuffix : remaining+(entries.drop remaining).length=n := by rw [List.length_drop,hLength]; omega
  have hFill := fill_bound index
    (if bits then GeneralPaperSummaryArrayExecution.arrayWord W (n+2) else W) W P remaining callback hCallback hc
    (entries.drop remaining) hSuffix (fun e he => hEntry e (List.mem_of_mem_drop he))
  have hn := GeneralPaperActualEpochInstructions.cell_count learner cache j
  have hResult := hFill.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (P+2*W) hn) _)
  exact Nat.add_le_add hResult (frames_mono W n (GeneralPaperBatchCounterPrice.limit k) hn)

end Blotto.GeneralPaperInstructionConstructionStorage
