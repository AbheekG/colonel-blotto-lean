import Blotto.GeneralPaperBatchCounterPrice

/-! Full batch bit price, using actual endpoint bounds, retained source
parameters and a cell-descriptor count cap. Final code effects derive every
successive input/output invariant; native full batch counters derive the
metadata words. No list-count, encoding or work-sum pass executes.
-/
namespace Blotto.GeneralPaperBatchUpdateBitPrice
open GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperIntervalBatch (Instruction effect)
open GeneralPaperBatchUpdateExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def rootProfile (price : ℕ → ℕ) (W m lambda k Qv height : ℕ) : ℕ :=
  (1+4*height)*GeneralPaperRangeUpdateBitPrice.nodeProfile price W m lambda k Qv+
    2*price (GeneralPaperDecoderControls.operandWidth lambda)+64*W

def entryProfile (price : ℕ → ℕ) (W m lambda k Qv height : ℕ) : ℕ :=
  rootProfile price W m lambda k Qv height+6*price (4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+256*W

theorem combine (u t z R Q W N : ℕ) (hu : u≤R) (ht : t≤N*(R+6*Q+256*W)+64*W) (hz : z≤6*Q) :
    u+t+z+256*W≤(N+1)*(R+6*Q+256*W)+64*W := by nlinarith

theorem counters (bits : Bool) (price : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (height : ℕ) (span : ℚ) (n : Node height) (entry : Instruction) (rest : List Instruction) :
    let updated := GeneralPaperRangeRootPrice.run bits price W c entry.lo entry.hi entry.amount height n span
    let tail := run bits price W c height span updated.1.node rest
    (run bits price W c height span n (entry::rest)).1.work=updated.1.work+tail.1.work+16 ∧
    (run bits price W c height span n (entry::rest)).1.visits=updated.1.visits+tail.1.visits := by
  dsimp only
  constructor <;> (conv_lhs => rw [GeneralPaperBatchUpdateExecution.run])

theorem work (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (height : ℕ) (span : ℚ) (n : Node height) (entries : List Instruction) (hSpan : span=(2:ℚ)^height)
    (hHeight : height≤lambda+1)
    (hEndpoints : ∀ entry∈entries,entry.lo≤2^(lambda+1) ∧ entry.hi≤2^(lambda+1))
    (hCount : entries.length≤GeneralPaperBatchCounterPrice.limit k) (hValid : Valid lambda k n)
    (hFinal : ∀ i<2^height,levelAt n i+effect entries i≤GeneralPaperPowerPrecision.levelBound lambda k) :
    (run true price W c height span n entries).2≤entries.length*entryProfile price W m lambda k Qv height+64*W := by
  have hPowers : c.powers=GeneralPaperPreparedPowers.prepare lambda k := by rw [hc]; rfl
  induction entries generalizing n with
  | nil => simp only [GeneralPaperBatchUpdateExecution.run,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons entry rest ih =>
    let updated := GeneralPaperRangeRootPrice.run true price W c entry.lo entry.hi entry.amount height n span
    let tail := run true price W c height span updated.1.node rest
    have hs := GeneralPaperBatchUpdateState.head_state lambda k height span n entry rest hSpan hValid hFinal
    have hu := GeneralPaperRangeRootPrice.grid_data true price W m lambda k Qv c hc entry.lo entry.hi entry.amount height n span hSpan hValid hs.1
    have hValidUpdated : Valid lambda k updated.1.node := by rw [hu,hPowers]; exact hs.2.1
    have hRestFinal : ∀ i<2^height,levelAt updated.1.node i+effect rest i≤GeneralPaperPowerPrecision.levelBound lambda k := by
      rw [hu,hPowers]
      exact hs.2.2
    have he := hEndpoints entry (by simp only [List.mem_cons_self])
    have hTailEndpoints : ∀ e∈rest,e.lo≤2^(lambda+1) ∧ e.hi≤2^(lambda+1) :=
      fun e he => hEndpoints e (List.mem_cons_of_mem entry he)
    have hTailCount : rest.length≤GeneralPaperBatchCounterPrice.limit k := by
      change rest.length+1≤GeneralPaperBatchCounterPrice.limit k at hCount
      omega
    have ht := ih updated.1.node hTailEndpoints hTailCount hValidUpdated hRestFinal
    have hh := GeneralPaperRangeUpdateBitPrice.root_work price hMono W m lambda k Qv c hc entry.lo entry.hi entry.amount height n span
      hSpan hHeight he.1 he.2 hValid hs.1
    have hb : (run true price W c height span n (entry::rest)).1.work≤GeneralPaperBatchCounterPrice.cap lambda k ∧
        (run true price W c height span n (entry::rest)).1.visits≤GeneralPaperBatchCounterPrice.cap lambda k := by
      rw [GeneralPaperBatchUpdateExecution.data true price W m lambda k Qv c hc height span n (entry::rest) hSpan hValid hFinal,hPowers]
      exact GeneralPaperBatchCounterPrice.native_cap lambda k height span n (entry::rest) hHeight (by rw [hSpan]; positivity) hCount
    have parts := counters true price W c height span n entry rest
    rw [parts.1,parts.2] at hb
    have hm := GeneralPaperBatchCounterPrice.metadata_work price hMono updated.1 tail.1 _ _ hb.1 hb.2
      (GeneralPaperBatchCounterPrice.operand_width m lambda k Qv)
    rw [GeneralPaperBatchUpdateExecution.run]
    dsimp only
    exact combine updated.2 tail.2 _ (rootProfile price W m lambda k Qv height)
      (price (4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) W rest.length hh ht hm

end Blotto.GeneralPaperBatchUpdateBitPrice
