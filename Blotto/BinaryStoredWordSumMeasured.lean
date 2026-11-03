import Blotto.BinaryPRGPromiseControlMeasured
import Blotto.BinaryStoredWordSumLifetime

/-! The actual tail-to-head quadratic sum returns every reached addition
with its trace/work. Arbitrary canonical words, including rejected inputs,
derive operand bounds from stored-width credit; unit mass is not assumed. -/
namespace Blotto.BinaryStoredWordSumMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryPRGRecognition
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryStoredWordSumWork
set_option autoImplicit false

def sum : List SignedWord → (SignedWord × Trace) × ℕ
  | [] => ((zero,wrap 8 1 []),4)
  | word::rest =>
      let tail := sum rest
      let head := BinaryQuadraticMeasured.apply .add word tail.1.1
      ((head.1.1,wrap 24 2 [tail.1.2,head.1.2]),tail.2+head.2+8)

theorem sum_erases (words : List SignedWord) : (sum words).1 = BinaryStoredWordSumLifetime.sumWithTrace words := by
  induction words with
  | nil => rfl
  | cons word rest ih => simp only [sum,BinaryStoredWordSumLifetime.sumWithTrace,ih,BinaryQuadraticMeasured.apply_erases]

theorem sum_data (words : List SignedWord) (hC : ∀ word ∈ words,CanonicalWord word) :
    (sum words).1.1 = sumWords words := by
  rw [sum_erases]
  exact BinaryStoredWordSumLifetime.sumWithTrace_state words hC

def price (count W : ℕ) : ℕ := (count+1)*(BinaryPRGPromiseControlMeasured.opcodePrice W+16)

theorem sum_work (words : List SignedWord) (hC : ∀ word ∈ words,CanonicalWord word)
    (W : ℕ) (hCredit : 1+2*credit words ≤ W) : (sum words).2 ≤ price words.length W := by
  induction words with
  | nil => simp only [sum,price,List.length_nil,Nat.zero_add,one_mul]; omega
  | cons word rest ih =>
      have ht : ∀ item ∈ rest,CanonicalWord item := fun item hi => hC item (by simp [hi])
      have hTailCredit := credit_tail word rest
      have hHead := credit_member (word::rest) word (by simp)
      have hW : width word ≤ W := by omega
      have hTailWidth : width (sum rest).1.1 ≤ W := by
        rw [sum_data rest ht]
        have hh := (sumWords_canonical rest ht).2.trans (rationalWordWidth_of_height (sum_height rest ht))
        omega
      have hOp := BinaryPRGPromiseControlMeasured.opcode_bound .add word (sum rest).1.1 W hW hTailWidth
      have hTail := ih ht (by omega)
      change (sum rest).2+(BinaryQuadraticMeasured.apply .add word (sum rest).1.1).2+8 ≤ _
      unfold price at hTail ⊢
      simp only [List.length_cons,Nat.add_mul,one_mul] at hTail ⊢
      omega

theorem sum_usage (words : List SignedWord) (hC : ∀ word ∈ words,CanonicalWord word)
    (W : ℕ) (hCredit : 1+2*credit words ≤ W) :
    usage (sum words).1.2 ≤ BinaryStoredWordSumLifetime.envelope words.length W := by
  rw [sum_erases]
  exact BinaryStoredWordSumLifetime.sumWithTrace_usage words hC W hCredit

theorem all_prefix (words : List SignedWord) (hC : ∀ word ∈ words,CanonicalWord word)
    (W : ℕ) (hCredit : 1+2*credit words ≤ W) (borrowed steps : ℕ) :
    retainedHeap borrowed (sum words).1.2 steps ≤ borrowed+BinaryStoredWordSumLifetime.envelope words.length W ∧
    framePeak ((sum words).1.2.take steps) ≤ BinaryStoredWordSumLifetime.envelope words.length W :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (sum_usage words hC W hCredit) _ steps

end Blotto.BinaryStoredWordSumMeasured
