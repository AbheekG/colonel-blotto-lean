import Blotto.GeneralPaperBatchUpdateArithmetic

/-! Returned cell capacities bound batch annotation words. The source's
largest signed cell count is 6*s+6. Native range work/visits derive each
batch counter cap, including every suffix, without counting the list again.
-/
namespace Blotto.GeneralPaperBatchCounterPrice
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalBatch
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def limit (k : ℕ) : ℕ := 6*(GeneralPaperSourceParameters.prepare k).summarySize+6

def cap (lambda k : ℕ) : ℕ := (limit k+1)*(GeneralPaperRangeCounterPrice.cap lambda k+64)

theorem limit_word (k : ℕ) : 1+binaryWordWidth (limit k+1)≤128+8*k := by
  have hs := (GeneralPaperSourceParameters.data k).2.2.2.2.2
  have hp := GeneralPaperNatPowerOperands.power_width 2 (34+k)
  have hm := binaryWordWidth_mul 6 (GeneralPaperSourceParameters.prepare k).summarySize
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (6*(GeneralPaperSourceParameters.prepare k).summarySize) 7
  have h2 : binaryWordWidth 2=2 := by decide
  have h6 : binaryWordWidth 6=3 := by decide
  have h7 : binaryWordWidth 7=3 := by decide
  rw [hs] at hm ha
  rw [h2] at hp
  unfold limit
  rw [hs]
  change 1+binaryWordWidth (6*2^(34+k)+7)≤128+8*k
  omega

theorem operand_width (m lambda k Qv : ℕ) : 1+binaryWordWidth (cap lambda k)≤
    4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hRange := GeneralPaperRangeCounterPrice.operand_width m lambda k Qv
  have hLimit := limit_word k
  have hAdd := GeneralPaperRayOperandWidthEnvelope.word_add (GeneralPaperRangeCounterPrice.cap lambda k) 64
  have hProduct := binaryWordWidth_mul (limit k+1) (GeneralPaperRangeCounterPrice.cap lambda k+64)
  have h64 : binaryWordWidth 64=7 := by decide
  have hk := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  unfold cap GeneralPaperPowerPreparationEnvelope.operandWidth at *
  omega

theorem aggregate (u t v q C N : ℕ) (hu : u≤C) (ht : t≤N*(C+16)+8) (hv : v≤C) (hq : q≤N*C) :
    u+t+16≤(N+1)*(C+16)+8 ∧ v+q≤(N+1)*C := by constructor <;> nlinarith

theorem native_bounds (lambda k height : ℕ) (span : ℚ) (n : Node height) (entries : List Instruction)
    (hHeight : height≤lambda+1) (hSpan : 0<span) :
    (GeneralPaperIntervalBatch.run (GeneralPaperPreparedPowers.prepare lambda k) height span n entries).work≤
        entries.length*(GeneralPaperRangeCounterPrice.cap lambda k+16)+8 ∧
    (GeneralPaperIntervalBatch.run (GeneralPaperPreparedPowers.prepare lambda k) height span n entries).visits≤
        entries.length*GeneralPaperRangeCounterPrice.cap lambda k := by
  induction entries generalizing n with
  | nil => simp only [GeneralPaperIntervalBatch.run,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl,and_self]
  | cons entry rest ih =>
    let updated := GeneralPaperIntervalUpdate.run (GeneralPaperPreparedPowers.prepare lambda k) entry.lo entry.hi entry.amount height n 0 span
    let tail := GeneralPaperIntervalBatch.run (GeneralPaperPreparedPowers.prepare lambda k) height span updated.node rest
    have hu := GeneralPaperRangeCounterPrice.native_bounds lambda k entry.lo entry.hi entry.amount height n 0 span hHeight hSpan
    have ht := ih updated.node
    exact aggregate updated.work tail.work updated.visits tail.visits _ rest.length hu.1 ht.1 hu.2 ht.2

theorem capped (w v R N : ℕ) (hw : w≤N*(R+16)+8) (hv : v≤N*R) :
    w≤(N+1)*(R+64) ∧ v≤(N+1)*(R+64) := by constructor <;> nlinarith

theorem native_cap (lambda k height : ℕ) (span : ℚ) (n : Node height) (entries : List Instruction)
    (hHeight : height≤lambda+1) (hSpan : 0<span) (hCount : entries.length≤limit k) :
    (GeneralPaperIntervalBatch.run (GeneralPaperPreparedPowers.prepare lambda k) height span n entries).work≤cap lambda k ∧
    (GeneralPaperIntervalBatch.run (GeneralPaperPreparedPowers.prepare lambda k) height span n entries).visits≤cap lambda k := by
  have hb := native_bounds lambda k height span n entries hHeight hSpan
  have hw := hb.1.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hCount) 8)
  have hv := hb.2.trans (Nat.mul_le_mul_right _ hCount)
  exact capped _ _ _ (limit k) hw hv

theorem metadata_work {height : ℕ} (price : ℕ → ℕ) (hMono : Monotone price)
    (updated : GeneralPaperIntervalUpdate.Result height) (tail : GeneralPaperIntervalBatch.Result height) (C H : ℕ)
    (hWork : updated.work+tail.work+16≤C) (hVisits : updated.visits+tail.visits≤C)
    (hWidth : 1+binaryWordWidth C≤H) :
    GeneralPaperBatchUpdateExecution.metadataCost price updated tail≤6*price H := by
  have hA := GeneralPaperPowerTableBounds.metadata_work price hMono updated.work tail.work 16 C H hWork hWidth
  have hB := (GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) updated.visits tail.visits C
    (by omega) (by omega) hVisits).trans (Nat.mul_le_mul_left 2 (hMono hWidth))
  unfold GeneralPaperBatchUpdateExecution.metadataCost
  omega

end Blotto.GeneralPaperBatchCounterPrice
