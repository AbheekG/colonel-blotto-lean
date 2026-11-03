import Blotto.GeneralPaperBatchUpdateState

/-! Execute the retained instruction list once. Each root range call and
all native batch work/visit additions share their actual returned records.
The final node, work and visits equal the complete native batch result.
-/
namespace Blotto.GeneralPaperBatchUpdateExecution
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalBatch
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def metadataCost (price : ℕ → ℕ) {height : ℕ} (updated : GeneralPaperIntervalUpdate.Result height)
    (tail : GeneralPaperIntervalBatch.Result height) : ℕ :=
  GeneralPaperPowerTableBounds.metadataCost price updated.work tail.work 16+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) updated.visits tail.visits

def run (bits : Bool) (price : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (height : ℕ) (span : ℚ) (n : Node height) : List Instruction → GeneralPaperIntervalBatch.Result height × ℕ
  | [] => (⟨n,8,0⟩,64*W)
  | entry::rest =>
    let updated := GeneralPaperRangeRootPrice.run bits price W c entry.lo entry.hi entry.amount height n span
    let tail := run bits price W c height span updated.1.node rest
    (⟨tail.1.node,updated.1.work+tail.1.work+16,updated.1.visits+tail.1.visits⟩,
      updated.2+tail.2+metadataCost (if bits then price else fun _ => 1) updated.1 tail.1+256*W)

theorem data (bits : Bool) (price : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (height : ℕ) (span : ℚ) (n : Node height) (entries : List Instruction) (hSpan : span=(2:ℚ)^height)
    (hValid : Valid lambda k n)
    (hFinal : ∀ i<2^height,levelAt n i+effect entries i≤GeneralPaperPowerPrecision.levelBound lambda k) :
    (run bits price W c height span n entries).1=GeneralPaperIntervalBatch.run c.powers height span n entries := by
  have hPowers : c.powers=GeneralPaperPreparedPowers.prepare lambda k := by rw [hc]; rfl
  induction entries generalizing n with
  | nil => rfl
  | cons entry rest ih =>
    have hs := GeneralPaperBatchUpdateState.head_state lambda k height span n entry rest hSpan hValid hFinal
    have hu := GeneralPaperRangeRootPrice.grid_data bits price W m lambda k Qv c hc entry.lo entry.hi entry.amount height n span hSpan hValid hs.1
    have hv : Valid lambda k (GeneralPaperIntervalUpdate.run c.powers entry.lo entry.hi entry.amount height n 0 span).node := by
      rw [hPowers]
      exact hs.2.1
    have ht : ∀ i<2^height,levelAt (GeneralPaperIntervalUpdate.run c.powers entry.lo entry.hi entry.amount height n 0 span).node i+
        effect rest i≤GeneralPaperPowerPrecision.levelBound lambda k := by
      rw [hPowers]
      exact hs.2.2
    rw [run]
    dsimp only
    rw [hu,ih _ hv ht]
    rfl

theorem metadata_arithmetic {height : ℕ} (updated : GeneralPaperIntervalUpdate.Result height)
    (tail : GeneralPaperIntervalBatch.Result height) : metadataCost (fun _ => 1) updated tail=6 := rfl

theorem same_data (price : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (height : ℕ) (span : ℚ) (n : Node height) (entries : List Instruction) (hSpan : span=(2:ℚ)^height)
    (hValid : Valid lambda k n)
    (hFinal : ∀ i<2^height,levelAt n i+effect entries i≤GeneralPaperPowerPrecision.levelBound lambda k) :
    (run true price W c height span n entries).1=(run false price 1 c height span n entries).1 := by
  rw [data true price W m lambda k Qv c hc height span n entries hSpan hValid hFinal,
    data false price 1 m lambda k Qv c hc height span n entries hSpan hValid hFinal]

end Blotto.GeneralPaperBatchUpdateExecution
