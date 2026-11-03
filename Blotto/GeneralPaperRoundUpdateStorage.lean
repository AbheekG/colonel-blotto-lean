import Blotto.GeneralPaperEncodedTrajectoryStorage

/-! Actual indexed all-field update prefixes reserve the complete output
reference buffer. Its window includes the old family, completed new fields,
one current delta/result field and the common pre-update snapshot. Primitive
scratch and shared plan/cache workspaces remain separate. -/
namespace Blotto.GeneralPaperRoundUpdateStorage
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem next_field {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ) (j : Fin m) :
    let current := GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br
    (GeneralPaperRoundFieldsExecution.element bits index price W (GeneralPaperSourceParameters.prepare k).meshDenominator
      (stateAt current time) (beforeAt current time) (rowsAt current time) j).1=fieldAt current (time+1) j := by
  dsimp only
  rw [GeneralPaperRoundFieldsExecution.element_data bits index price W _ _ _ _ j rfl]
  exact (field_step (GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br) time j).symm

theorem next_field_bound {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    let current := GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br
    GeneralPaperEncodedEpochLevels.fieldFootprint W
      (GeneralPaperRoundFieldsExecution.element bits index price W (GeneralPaperSourceParameters.prepare k).meshDenominator
        (stateAt current time) (beforeAt current time) (rowsAt current time) j).1≤
      GeneralPaperEncodedEpochLevels.fieldProfile W m cache.alphabet.lambda k Qv := by
  dsimp only
  rw [next_field bits index price W Qv cache weights Bc Br time j]
  exact GeneralPaperEncodedEpochLevels.field_bound W m cache.alphabet.lambda Qv _
    (GeneralPaperEncodedEpochLevels.actual_counts cache _ j (field_plan _ (time+1) j))
    (selected_cap cache Qv weights Bc Br (time+1) ht j)

theorem output_prefix {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (count : ℕ) (hc : count≤m) :
    let current := GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br
    GeneralPaperEncodedReferenceVector.reservedFootprint W m (GeneralPaperEncodedEpochLevels.fieldFootprint W)
      (PaperIndexedArrayConstruction.fill index (if bits then GeneralPaperSummaryArrayExecution.arrayWord W m else W)
        (GeneralPaperRoundFieldsExecution.element bits index price W (GeneralPaperSourceParameters.prepare k).meshDenominator
          (stateAt current time) (beforeAt current time) (rowsAt current time)) count hc).1≤
      GeneralPaperEncodedEpochLevels.profile W m cache.alphabet.lambda k Qv := by
  have h := GeneralPaperEncodedReferenceVector.indexed_reserved_prefix index
    (if bits then GeneralPaperSummaryArrayExecution.arrayWord W m else W) W
    (GeneralPaperEncodedEpochLevels.fieldProfile W m cache.alphabet.lambda k Qv)
    (GeneralPaperEncodedEpochLevels.fieldFootprint W) _
    (next_field_bound bits index price W Qv cache weights Bc Br time ht) count hc
  exact h.trans_eq (by unfold GeneralPaperEncodedEpochLevels.profile; ring)

def window {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time count : ℕ) (hc : count≤m) (j : Fin m) : ℕ :=
  let current := GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br
  let callback := GeneralPaperRoundFieldsExecution.element bits index price W (GeneralPaperSourceParameters.prepare k).meshDenominator
    (stateAt current time) (beforeAt current time) (rowsAt current time)
  GeneralPaperEncodedEpochLevels.familyFootprint W (stateAt current time).fields+
    GeneralPaperEncodedReferenceVector.reservedFootprint W m (GeneralPaperEncodedEpochLevels.fieldFootprint W)
      (PaperIndexedArrayConstruction.fill index (if bits then GeneralPaperSummaryArrayExecution.arrayWord W m else W) callback count hc).1+
    GeneralPaperEncodedEpochLevels.fieldFootprint W (GeneralPaperEncodedEpochLevels.deltaView (deltaAt current time j))+
    GeneralPaperEncodedEpochLevels.fieldFootprint W (callback j).1+
    GeneralPaperEncodedSnapshotStorage.familyFootprint W (beforeAt current time)

def profile (W m lambda k Qv : ℕ) : ℕ :=
  2*GeneralPaperEncodedEpochLevels.profile W m lambda k Qv+2*GeneralPaperEncodedEpochLevels.fieldProfile W m lambda k Qv+
    GeneralPaperEncodedSnapshotStorage.profile W m lambda k Qv

theorem window_bound {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ) (cache : Cache m k)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time+1≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (count : ℕ) (hc : count≤m) (j : Fin m) :
    window bits index price W Qv cache weights Bc Br time count hc j≤profile W m cache.alphabet.lambda k Qv := by
  have hTime : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period := by omega
  have hs := GeneralPaperEncodedEpochLevels.selected W Qv cache weights Bc Br time hTime
  have hp := output_prefix bits index price W Qv cache weights Bc Br time ht count hc
  have hd := GeneralPaperEncodedEpochLevels.generated W Qv cache weights Bc Br time hTime j
  have hn := next_field_bound bits index price W Qv cache weights Bc Br time ht j
  have hb := GeneralPaperEncodedSnapshotStorage.selected W Qv cache weights Bc Br time hTime
  have h := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hs hp) hd) hn) hb
  exact h.trans_eq (by unfold profile; ring)

theorem recorded_codes {m k : ℕ} (W : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (row : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))) :
    GeneralPaperEncodedTrajectoryStorage.rowFootprint W (GeneralPaperCatalogueRowSemantics.rowCodes ready.data row)≤
      m*(GeneralPaperDecoderControls.operandWidth ready.alphabet.lambda+W)+64*W := by
  have h := GeneralPaperEncodedNatArray.bounded W (GeneralPaperDecoderControls.operandWidth ready.alphabet.lambda)
    (GeneralPaperCatalogueRowSemantics.rowCodes ready.data row) (by
      intro j
      rw [GeneralPaperCatalogueRowSemantics.rowCodes,FixedArrayTable.read_ofFn]
      exact GeneralPaperSelectedRowCodesPrice.code_word ready row j)
  exact (Nat.add_le_add_right h (32*W)).trans_eq (by ring)

end Blotto.GeneralPaperRoundUpdateStorage
