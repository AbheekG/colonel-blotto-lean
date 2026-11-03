import Blotto.GeneralPaperEqualPowerWidthCapacity

/-! Fused stored-word encoding retains reached quotient/remainder data,
primitive scratch, output cells and work/control fields. The observer sums
pending recursive activations and selected suffixes, without another pass. -/
namespace Blotto.GeneralPaperWordEncodingLifetime
open GeneralPaperStoredWordEncoding (run word)
open GeneralPaperEncodedScalarStorage (natBits fields listFootprint)
set_option autoImplicit false
set_option maxHeartbeats 1800000

def bitListProfile (A width : ℕ) : ℕ := width * (1 + 2 * A) + 32 * A

theorem list_bound (A width : ℕ) (bits : List Bool) (h : bits.length ≤ width) :
    listFootprint A (fun _ : Bool => 1) bits ≤ bitListProfile A width :=
  (GeneralPaperEncodedScalarStorage.list_bound A 1 (fun _ : Bool => 1) bits (by intro _ _; exact le_rfl)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _)

def localFoot (model : RationalCostModel) (A length n : ℕ) : ℕ :=
  let child := run model A length (n / 2)
  let actual := run model A (length + 1) n
  natBits n + natBits (n / 2) + natBits (n % 2) + 1 + 4 * model.rat (binaryWordWidth n + 3) +
    fields A [length, child.2, actual.2] + 128 * A

theorem local_bound (model : RationalCostModel) (A length n : ℕ) :
    localFoot model A length n ≤ 256 * (run model A (length + 1) n).2 := by
  let F := (run model A (length + 1) n).2
  let child := run model A length (n / 2)
  have hF : F = child.2 + binaryWordWidth n + binaryWordWidth (n / 2) + binaryWordWidth (n % 2) +
      4 * model.rat (binaryWordWidth n + 3) + 64 * (A + binaryWordWidth (length + 2) + 1) := rfl
  have hIndex := Nat.add_le_add_left (binaryWordWidth_mono (show length ≤ length + 2 by omega)) 1
  change natBits length ≤ 1 + binaryWordWidth (length + 2) at hIndex
  have hFields := GeneralPaperEncodedScalarStorage.fields_bound A (F + 2) [length, child.2, F] (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · omega
    · exact (GeneralPaperNaturalScalarLifetime.counter_word _).trans (by omega)
    · exact GeneralPaperNaturalScalarLifetime.counter_word _)
  change fields A _ ≤ 3 * (F + 2 + A) + 32 * A at hFields
  change natBits n + natBits (n / 2) + natBits (n % 2) + 1 + 4 * model.rat (binaryWordWidth n + 3) +
    fields A [length, child.2, F] + 128 * A ≤ 256 * F
  unfold natBits
  omega

def live (model : RationalCostModel) (A : ℕ) : ℕ → ℕ → ℕ
  | 0, n => natBits n + fields A [(run model A 0 n).2] + 64 * A
  | length + 1, n => localFoot model A length n +
      listFootprint A (fun _ : Bool => 1) (run model A (length + 1) n).1 + live model A length (n / 2)

def time (model : RationalCostModel) (A width L : ℕ) : ℕ :=
  width * GeneralPaperStoredWordEncoding.stepBound model A width L + 64 * A + 64

def profile (model : RationalCostModel) (A width L : ℕ) : ℕ :=
  (width + 1) * (256 * time model A width L + bitListProfile A width + L + 1 + 64 * A)

theorem bounded (model : RationalCostModel) (A width L length n : ℕ) (hl : length ≤ width) (hn : binaryWordWidth n ≤ L) :
    live model A length n ≤ (length + 1) * (256 * time model A width L + bitListProfile A width + L + 1 + 64 * A) := by
  induction length generalizing n with
  | zero =>
    have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (64 * A + 64) [64 * A + 64]
      (by intro x hx; exact (List.mem_singleton.mp hx).le)
    simp only [List.length_singleton, one_mul] at hFields
    have hCounter := GeneralPaperNaturalScalarLifetime.counter_word (64 * A + 64)
    simp only [live, run, Nat.zero_add, one_mul]
    unfold time natBits
    omega
  | succ length ih =>
    have hWork : (run model A (length + 1) n).2 ≤ time model A width L :=
      (GeneralPaperStoredWordEncoding.bounded_work model A width L (length + 1) hl n hn).trans
        (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) _) _)
    have hLocal := (local_bound model A length n).trans (Nat.mul_le_mul_left 256 hWork)
    have hList := list_bound A width (run model A (length + 1) n).1 (by
      rw [GeneralPaperStoredWordEncoding.data, BinaryPayload.bits_length]; exact hl)
    have hChild := ih (n / 2) (by omega) ((binaryWordWidth_mono (Nat.div_le_self n 2)).trans hn)
    simp only [live]
    nlinarith only [hLocal, hList, hChild]

def window (model : RationalCostModel) (A width n : ℕ) : ℕ :=
  live model A width n + GeneralPaperEqualRetainedStorage.wordFoot A (word model A width n).1 +
    fields A [width, (word model A width n).2] + 64 * A

def windowProfile (model : RationalCostModel) (A width L : ℕ) : ℕ :=
  profile model A width L + GeneralPaperEqualRetainedStorage.wordProfile A width +
    2 * (natBits (width + time model A width L + 1) + A) + 96 * A

theorem word_bound (model : RationalCostModel) (A width n L : ℕ) (hn : binaryWordWidth n ≤ L) :
    window model A width n ≤ windowProfile model A width L := by
  have hLive := bounded model A width L width n le_rfl hn
  have hPayload := GeneralPaperEqualRetainedStorage.word_bound A (word model A width n).1
  have hTime : (word model A width n).2 ≤ time model A width L := GeneralPaperStoredWordEncoding.work model A width n L hn
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (width + time model A width L + 1)
    [width, (word model A width n).2] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> omega)
  change fields A _ ≤ 2 * (natBits (width + time model A width L + 1) + A) + 32 * A at hFields
  unfold window windowProfile profile
  omega

end Blotto.GeneralPaperWordEncodingLifetime
