import Blotto.GeneralPaperActualEpochInstructions

/-! One retained epoch node consumes one instruction construction and one
complete batch execution. Native final arrays supply all counts/endpoints;
state effect caps derive every range-state premise. Retained spans and power
caches are reused; no epoch, source or validation pass is reconstructed.
-/
namespace Blotto.GeneralPaperEpochNodeUpdate
open GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueOccurrenceHistory
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {m k : ℕ} {cache : Cache m k} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (learner : Learner) (state : State cache) (j : Fin m)
    (height : ℕ) (n : Node height) (span : ℚ) : GeneralPaperIntervalBatch.Result height × ℕ :=
  let made := GeneralPaperActualEpochInstructions.run bits index W learner state j
  let updated := GeneralPaperBatchUpdateExecution.run bits price W c height span n made.1
  (updated.1,made.2+updated.2+64*W)

def profile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  let count := GeneralPaperBatchCounterPrice.limit k
  GeneralPaperCellInstructionPrice.profile W count+
    (count*GeneralPaperBatchUpdateBitPrice.entryProfile price W m lambda k Qv (lambda+1)+64*W)+64*W

def arithmeticProfile (m lambda k Qv : ℕ) : ℕ :=
  let count := GeneralPaperBatchCounterPrice.limit k
  GeneralPaperCellInstructionPrice.arithmeticProfile count+
    (count*GeneralPaperBatchUpdateArithmetic.entryProfile m lambda k Qv (lambda+1)+64)+64

theorem bit_entry_mono (price : ℕ → ℕ) (W m lambda k Qv h H : ℕ) (hHeight : h≤H) :
    GeneralPaperBatchUpdateBitPrice.entryProfile price W m lambda k Qv h≤
      GeneralPaperBatchUpdateBitPrice.entryProfile price W m lambda k Qv H := by
  have hw := Nat.mul_le_mul_right (GeneralPaperRangeUpdateBitPrice.nodeProfile price W m lambda k Qv)
    (show 1+4*h≤1+4*H by omega)
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hw
    (2*price (GeneralPaperDecoderControls.operandWidth lambda))) (64*W))
      (6*price (4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv))) (256*W)

theorem arithmetic_entry_mono (m lambda k Qv h H : ℕ) (hHeight : h≤H) :
    GeneralPaperBatchUpdateArithmetic.entryProfile m lambda k Qv h≤
      GeneralPaperBatchUpdateArithmetic.entryProfile m lambda k Qv H :=
  Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right (GeneralPaperRangeUpdateArithmetic.nodeProfile m lambda k Qv)
    (show 1+4*h≤1+4*H by omega)) 66) 262

theorem data {m k : ℕ} {cache : Cache m k} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (learner : Learner) (state : State cache) (j : Fin m) (height : ℕ) (n : Node height) (span : ℚ)
    (hSpan : span=(2:ℚ)^height) (hValid : Valid cache.alphabet.lambda k n)
    (hFinal : ∀ i<2^height,levelAt n i+GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i≤
      GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) :
    (run bits index price W c learner state j height n span).1=
      GeneralPaperIntervalBatch.run c.powers height span n (GeneralPaperCatalogueCellHistory.batchOfState learner state j) := by
  let made := GeneralPaperActualEpochInstructions.run bits index W learner state j
  have hf : ∀ i<2^height,levelAt n i+GeneralPaperIntervalBatch.effect made.1 i≤GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k := by
    rw [GeneralPaperActualEpochInstructions.data]
    exact hFinal
  unfold run
  dsimp only
  rw [GeneralPaperBatchUpdateExecution.data bits price W m cache.alphabet.lambda k Qv c hc height span n made.1 hSpan hValid hf,
    GeneralPaperActualEpochInstructions.data]

theorem bit_work {m k : ℕ} {cache : Cache m k} (price : ℕ → ℕ) (hMono : Monotone price) (W Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (learner : Learner) (state : State cache) (j : Fin m) (height : ℕ) (n : Node height) (span : ℚ)
    (hSpan : span=(2:ℚ)^height) (hHeight : height≤cache.alphabet.lambda+1) (hValid : Valid cache.alphabet.lambda k n)
    (hFinal : ∀ i<2^height,levelAt n i+GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i≤
      GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) :
    (run true (fun w => w) price W c learner state j height n span).2≤profile price W m cache.alphabet.lambda k Qv := by
  let made := GeneralPaperActualEpochInstructions.run true (fun w => w) W learner state j
  have hf : ∀ i<2^height,levelAt n i+GeneralPaperIntervalBatch.effect made.1 i≤GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k := by
    rw [GeneralPaperActualEpochInstructions.data]
    exact hFinal
  have hi := GeneralPaperActualEpochInstructions.bit_work W learner state j
  have hn := GeneralPaperActualEpochInstructions.length true (fun w => w) W learner state j
  have he := GeneralPaperActualEpochInstructions.endpoints true (fun w => w) W learner state j
  have hb := GeneralPaperBatchUpdateBitPrice.work price hMono W m cache.alphabet.lambda k Qv c hc height span n made.1
    hSpan hHeight he hn hValid hf
  have hLift := Nat.add_le_add_right (Nat.mul_le_mul hn
    (bit_entry_mono price W m cache.alphabet.lambda k Qv height (cache.alphabet.lambda+1) hHeight)) (64*W)
  exact Nat.add_le_add_right (Nat.add_le_add hi (hb.trans hLift)) (64*W)

theorem arithmetic_work {m k : ℕ} {cache : Cache m k} (price : ℕ → ℕ) (Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (learner : Learner) (state : State cache) (j : Fin m) (height : ℕ) (n : Node height) (span : ℚ)
    (hSpan : span=(2:ℚ)^height) (hHeight : height≤cache.alphabet.lambda+1) (hValid : Valid cache.alphabet.lambda k n)
    (hFinal : ∀ i<2^height,levelAt n i+GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i≤
      GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) :
    (run false (fun _ => 1) price 1 c learner state j height n span).2≤arithmeticProfile m cache.alphabet.lambda k Qv := by
  let made := GeneralPaperActualEpochInstructions.run false (fun _ => 1) 1 learner state j
  have hf : ∀ i<2^height,levelAt n i+GeneralPaperIntervalBatch.effect made.1 i≤GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k := by
    rw [GeneralPaperActualEpochInstructions.data]
    exact hFinal
  have hi := GeneralPaperActualEpochInstructions.arithmetic_work learner state j
  have hn := GeneralPaperActualEpochInstructions.length false (fun _ => 1) 1 learner state j
  have hb := GeneralPaperBatchUpdateArithmetic.work price m cache.alphabet.lambda k Qv c hc height span n made.1 hSpan hValid hf
  have hLift := Nat.add_le_add_right (Nat.mul_le_mul hn
    (arithmetic_entry_mono m cache.alphabet.lambda k Qv height (cache.alphabet.lambda+1) hHeight)) 64
  exact Nat.add_le_add_right (Nat.add_le_add hi (hb.trans hLift)) 64

theorem same_data {m k : ℕ} {cache : Cache m k} (price : ℕ → ℕ) (W Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (learner : Learner) (state : State cache) (j : Fin m) (height : ℕ) (n : Node height) (span : ℚ)
    (hSpan : span=(2:ℚ)^height) (hValid : Valid cache.alphabet.lambda k n)
    (hFinal : ∀ i<2^height,levelAt n i+GeneralPaperIntervalBatch.effect (GeneralPaperCatalogueCellHistory.batchOfState learner state j) i≤
      GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) :
    (run true (fun w => w) price W c learner state j height n span).1=
      (run false (fun _ => 1) price 1 c learner state j height n span).1 := by
  rw [data true (fun w => w) price W Qv c hc learner state j height n span hSpan hValid hFinal,
    data false (fun _ => 1) price 1 Qv c hc learner state j height n span hSpan hValid hFinal]

end Blotto.GeneralPaperEpochNodeUpdate
