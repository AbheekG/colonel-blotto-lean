import Blotto.GeneralPaperEqualBooleanCache

/-! A complete rejection trial reads one fresh word, checks it against the
stored denominator by Boolean borrow, and selects from the stored count words
only on acceptance. All numeric values below occur solely in proofs. -/
namespace Blotto.GeneralPaperEqualBooleanTrial
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperEqualBooleanCache (Cache)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 700000

def readWord {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) {S : Type*} (next : S → Bool × S) (state : S) :
    (FixedBinaryWord (p.rangeBits + 1) × S) × ℕ × ℕ :=
  let result := GeneralPaperBooleanFreshWord.read next c.ruler state
  ((⟨result.1.1.bits, result.1.1.size.trans (congrArg (fun n => n + 1) c.ruler_length)⟩, result.1.2), result.2)

theorem readWord_counts {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) {S : Type*} (next : S → Bool × S) (state : S) :
    (readWord c next state).2.1 = p.rangeBits ∧ (readWord c next state).2.2 = 10 * p.rangeBits + 10 := by
  simpa only [readWord, c.ruler_length] using GeneralPaperBooleanFreshWord.read_counts next c.ruler state

theorem readWord_value {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (bits : Fin p.rangeBits → Bool) :
    (readWord c GeneralPaperBooleanFreshWord.nextList (List.ofFn bits)).1.1.value = (balancedBitIndex p.rangeBits bits).val := by
  have h := GeneralPaperBooleanFreshWord.read_list c.ruler (List.ofFn bits) [] (by simp [c.ruler_length])
  simp only [List.append_nil] at h
  change BinaryBigEndian.littleValue _ = _
  dsimp only [readWord]
  rw [h.1, BinaryWordHighBit.littleValue_append]
  simp only [BinaryBigEndian.littleValue, Nat.mul_zero, Nat.add_zero, Bool.false_eq_true, ite_false]
  rw [GeneralPaperBooleanFreshWord.list_value, balancedBitIndex_eq]

structure Result (α S : Type*) where
  output : Option α
  state : S
  reads : ℕ
  work : ℕ

def run {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) {S : Type*} (next : S → Bool × S) (state : S) : Result (Fin (count l)) S :=
  let read := readWord c next state
  let compared := GeneralPaperBooleanBorrow.subtract read.1.1 c.denominator
  if compared.2.1 then
    let selected := GeneralPaperBooleanCategoricalSelect.run c.rows read.1.1
    ⟨selected.1, read.1.2, read.2.1, read.2.2 + compared.2.2 + selected.2 + 12⟩
  else ⟨none, read.1.2, read.2.1, read.2.2 + compared.2.2 + 8⟩

theorem reads {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) {S : Type*} (next : S → Bool × S) (state : S) : (run c next state).reads = p.rangeBits := by
  unfold run
  dsimp only
  split <;> exact (readWord_counts c next state).1

def bound {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) : ℕ := count l * (22 * (p.rangeBits + 1) + 16) + 32 * p.rangeBits + 54

theorem work {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) {S : Type*} (next : S → Bool × S) (state : S) : (run c next state).work ≤ bound p := by
  have hread := (readWord_counts c next state).2
  have hcomp := GeneralPaperBooleanBorrow.subtract_work (readWord c next state).1.1 c.denominator
  have hsel := GeneralPaperBooleanCategoricalSelect.work c.rows (readWord c next state).1.1
  rw [GeneralPaperEqualBooleanCache.rows_length] at hsel
  unfold run bound
  dsimp only
  split <;> dsimp only <;> omega

theorem output {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (bits : Fin p.rangeBits → Bool) :
    (run c GeneralPaperBooleanFreshWord.nextList (List.ofFn bits)).output =
      (GeneralPaperEqualPreparedCache.attempt p bits).map (GeneralPaperEqualPreparedCache.select p) := by
  let w := (readWord c GeneralPaperBooleanFreshWord.nextList (List.ofFn bits)).1.1
  have hv : w.value = (balancedBitIndex p.rangeBits bits).val := readWord_value c bits
  have hb : (GeneralPaperBooleanBorrow.subtract w c.denominator).2.1 = true ↔
      (balancedBitIndex p.rangeBits bits).val < p.D := by
    rw [GeneralPaperBooleanBorrow.borrow_iff, hv, c.denominator_value]
  unfold run
  dsimp only
  by_cases h : (balancedBitIndex p.rangeBits bits).val < p.D
  · rw [(hb.mpr h), ite_eq_left rfl]
    rw [GeneralPaperEqualBooleanCache.selection_data c w ⟨_, h⟩ hv]
    rw [GeneralPaperEqualPreparedCache.attempt, dite_eq_left h]
    rfl
  · have hf := Bool.eq_false_of_not_eq_true (fun hh => h (hb.mp hh))
    rw [hf, ite_eq_right Bool.false_ne_true, GeneralPaperEqualPreparedCache.attempt, dite_eq_right h]
    rfl

end Blotto.GeneralPaperEqualBooleanTrial
