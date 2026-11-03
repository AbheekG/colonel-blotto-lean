import Blotto.BinaryPRGPromiseControlLifetime

/-! The actual tail-to-head quadratic sum retains each returned addition.
Arbitrary canonical decoded words, including rejected games, supply a linear
height credit. No unit-sum or accepted-promise assumption enters the bound. -/
namespace Blotto.BinaryStoredWordSumLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryPRGRecognition
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryLifetimeUsage BinaryStoredWordSumWork

def sumWithTrace : List SignedWord → SignedWord × Trace
  | [] => (zero,wrap 8 1 [])
  | word::rest =>
      let tail := sumWithTrace rest
      let head := BinaryQuadraticLifetime.applyWithTrace .add word tail.1
      (head.1,wrap 24 2 [tail.2,head.2])

theorem sumWithTrace_state (words : List SignedWord) (hC : ∀ word ∈ words,CanonicalWord word) :
    (sumWithTrace words).1 = sumWords words := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
      have ht : ∀ item ∈ rest,CanonicalWord item := fun item hi => hC item (by simp [hi])
      simp only [sumWithTrace,ih ht]
      rw [BinaryQuadraticLifetime.applyWithTrace_state .add word (sumWords rest)
        (hC word (by simp)).1 (sumWords_canonical rest ht).1]
      rfl

def envelope (count W : ℕ) : ℕ := (count+1)*(opcodeEnvelope W+64)

theorem sumWithTrace_usage (words : List SignedWord) (hC : ∀ word ∈ words,CanonicalWord word)
    (W : ℕ) (hCredit : 1+2*credit words ≤ W) : usage (sumWithTrace words).2 ≤ envelope words.length W := by
  induction words with
  | nil =>
      have h := wrap_usage 8 1 []
      simp only [List.map_nil,List.sum_nil] at h
      change usage (wrap 8 1 []) ≤ _
      unfold envelope
      simp only [List.length_nil,Nat.zero_add,one_mul]
      omega
  | cons word rest ih =>
      have ht : ∀ item ∈ rest,CanonicalWord item := fun item hi => hC item (by simp [hi])
      have hTailCredit := credit_tail word rest
      have hHead := credit_member (word::rest) word (by simp)
      have hW : width word ≤ W := by omega
      have hTailWidth : width (sumWithTrace rest).1 ≤ W := by
        rw [sumWithTrace_state rest ht]
        have hh := (sumWords_canonical rest ht).2.trans (rationalWordWidth_of_height (sum_height rest ht))
        omega
      have hOp := opcode_usage .add word (sumWithTrace rest).1 W hW hTailWidth
      have hTail := ih ht (by omega)
      have hw := wrap_usage 24 2 [(sumWithTrace rest).2,
        (BinaryQuadraticLifetime.applyWithTrace .add word (sumWithTrace rest).1).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (sumWithTrace (word::rest)).2 ≤ _ at hw
      unfold envelope at hTail ⊢
      simp only [List.length_cons,Nat.add_mul,one_mul] at hTail ⊢
      omega

theorem all_prefix (words : List SignedWord) (hC : ∀ word ∈ words,CanonicalWord word)
    (W : ℕ) (hCredit : 1+2*credit words ≤ W) (borrowed steps : ℕ) :
    retainedHeap borrowed (sumWithTrace words).2 steps ≤ borrowed+envelope words.length W ∧
    framePeak ((sumWithTrace words).2.take steps) ≤ envelope words.length W :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (sumWithTrace_usage words hC W hCredit) borrowed steps

end Blotto.BinaryStoredWordSumLifetime
