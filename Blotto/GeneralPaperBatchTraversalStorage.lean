import Blotto.GeneralPaperRangeQueryStorage
import Blotto.GeneralPaperEncodedScalarStorage

/-! Range batches retain their instruction list and native annotations.
Owned tree payloads belong to the separate forest ledger. This observer
counts borrowed cursors, left-to-right batch frames and one range-query
window. It follows the native returned tree; it does not replay a batch. -/
namespace Blotto.GeneralPaperBatchTraversalStorage
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalBatch
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def instructionBits (W : ℕ) (e : Instruction) : ℕ :=
  natBits e.lo+natBits e.hi+natBits e.amount+64*W

def resultBits {height : ℕ} (W : ℕ) (r : Result height) : ℕ :=
  natBits r.work+natBits r.visits+64*W

def frame {height : ℕ} (W : ℕ) (span : ℚ) (e : Instruction)
    (updated : GeneralPaperIntervalUpdate.Result height) (tail : Result height) : ℕ :=
  instructionBits W e+GeneralPaperRangeTraversalStorage.resultBits W updated+
    resultBits W tail+natBits height+rationalWordWidth span+256*W

def peak (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (height : ℕ) (span : ℚ) : Node height → List Instruction → ℕ
  | n,[] => resultBits W (run c.powers height span n [])+natBits height+rationalWordWidth span+128*W
  | n,e::rest =>
    let updated := GeneralPaperIntervalUpdate.run c.powers e.lo e.hi e.amount height n 0 span
    let tail := run c.powers height span updated.node rest
    let controls := frame W span e updated tail+
      GeneralPaperBatchUpdateExecution.metadataCost model.rat updated tail
    controls+max (GeneralPaperRangeQueryStorage.window model W c e.lo e.hi e.amount height n span)
      (peak model W c height span updated.node rest)

def frameProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  4*GeneralPaperDecoderControls.operandWidth lambda+
    16*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+640*W+
    16*model.rat (4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)

def Good (lambda k : ℕ) (entries : List Instruction) : Prop :=
  ∀ e∈entries,e.lo≤2^(lambda+1) ∧ e.hi≤2^(lambda+1) ∧ e.amount≤GeneralPaperPowerPrecision.levelBound lambda k

theorem instruction_bound (W m lambda k Qv : ℕ) (e : Instruction)
    (hl : e.lo≤2^(lambda+1)) (hr : e.hi≤2^(lambda+1))
    (ha : e.amount≤GeneralPaperPowerPrecision.levelBound lambda k) :
    instructionBits W e≤2*GeneralPaperDecoderControls.operandWidth lambda+
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+64*W := by
  have a := GeneralPaperRangeGeometryPrice.natural_word lambda e.lo hl
  have b := GeneralPaperRangeGeometryPrice.natural_word lambda e.hi hr
  have c := (Nat.add_le_add_left (binaryWordWidth_mono ha) 1).trans (GeneralPaperFreshMassPrice.offset_width m lambda k Qv)
  unfold instructionBits natBits
  omega

theorem list_bound (W m lambda k Qv : ℕ) (entries : List Instruction) (hg : Good lambda k entries) :
    listFootprint W (instructionBits W) entries≤entries.length*
      (2*GeneralPaperDecoderControls.operandWidth lambda+
        GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+66*W)+32*W := by
  have h := GeneralPaperEncodedScalarStorage.list_bound W _ (instructionBits W) entries (fun e he => instruction_bound W m lambda k Qv e
    (hg e he).1 (hg e he).2.1 (hg e he).2.2)
  exact h.trans_eq (by ring)

theorem result_bound (W m lambda k Qv height : ℕ) (span : ℚ) (n : Node height) (entries : List Instruction)
    (hh : height≤lambda+1) (hs : 0<span) (hn : entries.length≤GeneralPaperBatchCounterPrice.limit k) :
    resultBits W (run (GeneralPaperPreparedPowers.prepare lambda k) height span n entries)≤
      8*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+64*W := by
  have h := GeneralPaperBatchCounterPrice.native_cap lambda k height span n entries hh hs hn
  have hw := GeneralPaperBatchCounterPrice.operand_width m lambda k Qv
  have a := binaryWordWidth_mono h.1
  have b := binaryWordWidth_mono h.2
  unfold resultBits natBits
  omega

theorem bounded (model : RationalCostModel) (W m lambda k Qv height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (span : ℚ) (n : Node height) (entries : List Instruction) (hs : span=(2:ℚ)^height)
    (hh : height≤lambda+1) (hn : entries.length≤GeneralPaperBatchCounterPrice.limit k)
    (hg : Good lambda k entries) (hv : Valid lambda k n)
    (hf : ∀ i<2^height,levelAt n i+effect entries i≤GeneralPaperPowerPrecision.levelBound lambda k) :
    peak model W c height span n entries≤(entries.length+1)*frameProfile model W m lambda k Qv+
      GeneralPaperRangeQueryStorage.profile model W m lambda k Qv height := by
  have hp : c.powers=GeneralPaperPreparedPowers.prepare lambda k := by rw [hc]; rfl
  have hSpan : 0<span := by rw [hs]; positivity
  have hH := GeneralPaperSparseNodeBits.height_word m lambda k Qv height hh
  have hS := GeneralPaperRangeGeometryPrice.rational_word lambda span
    (GeneralPaperRangeGeometryPrice.window_bounds lambda height 0 span (by rw [hs]; exact GeneralPaperRangeGeometryPrice.root_window lambda height hh)).2.1
  induction entries generalizing n with
  | nil =>
    have hR := result_bound W m lambda k Qv height span n [] hh hSpan (by simp)
    unfold peak
    rw [hp]
    unfold frameProfile natBits
    dsimp only [List.length_nil,Nat.zero_add,one_mul]
    omega
  | cons e rest ih =>
    have he := hg e (List.mem_cons_self ..)
    have hRest : Good lambda k rest := fun e he => hg e (List.mem_cons_of_mem _ he)
    have hState := GeneralPaperBatchUpdateState.head_state lambda k height span n e rest hs hv hf
    let updated := GeneralPaperIntervalUpdate.run c.powers e.lo e.hi e.amount height n 0 span
    let tail := run c.powers height span updated.node rest
    have hUpdated : updated=GeneralPaperIntervalUpdate.run (GeneralPaperPreparedPowers.prepare lambda k) e.lo e.hi e.amount height n 0 span := by dsimp [updated]; rw [hp]
    have hTail := ih updated.node (by simp only [List.length_cons] at hn; omega) hRest
      (by rw [hUpdated]; exact hState.2.1) (by rw [hUpdated]; exact hState.2.2)
    have hQuery := GeneralPaperRangeQueryStorage.bounded model W m lambda k Qv c hc e.lo e.hi e.amount height n span hs hh
      he.1 he.2.1 he.2.2 hv hState.1
    have hI := instruction_bound W m lambda k Qv e he.1 he.2.1 he.2.2
    have hU := GeneralPaperRangeTraversalStorage.result_bound W m lambda k Qv (e.lo:ℚ) e.hi e.amount height n 0 span hh hSpan
    rw [←hUpdated] at hU
    have hR := result_bound W m lambda k Qv height span updated.node rest hh hSpan (by simp only [List.length_cons] at hn; omega)
    rw [←hp] at hR
    have hC := GeneralPaperBatchCounterPrice.native_cap lambda k height span n (e::rest) hh hSpan hn
    rw [←hp] at hC
    change updated.work+tail.work+16≤_ ∧ updated.visits+tail.visits≤_ at hC
    have hMeta := GeneralPaperBatchCounterPrice.metadata_work model.rat model.monotone updated tail _ _ hC.1 hC.2
      (GeneralPaperBatchCounterPrice.operand_width m lambda k Qv)
    have hFrame : frame W span e updated tail+GeneralPaperBatchUpdateExecution.metadataCost model.rat updated tail≤
        frameProfile model W m lambda k Qv := by
      unfold frame frameProfile natBits
      change resultBits W tail≤_ at hR
      omega
    change _+max _ _≤(rest.length+1+1)*frameProfile model W m lambda k Qv+_
    have hMax := max_le (hQuery.trans (Nat.le_add_left _ _)) hTail
    exact (Nat.add_le_add hFrame hMax).trans_eq (by ring)

end Blotto.GeneralPaperBatchTraversalStorage
