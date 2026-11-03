import Blotto.BinaryLifetimeUsage
import Blotto.BinaryPRGPromiseWork

/-! Actual traced comparisons and delayed Boolean control used by the PRG
promise checker. A failed guard skips its continuation; list checks stop at
the first failure. Arithmetic operands remain borrowed and all reached
reservations/activations stay retained. -/
namespace Blotto.BinaryPRGPromiseControlLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryLifetimeUsage

def comparisonEnvelope (W : ℕ) : ℕ := 2500*(W+1)^3+150*(W+1)^2+16

theorem comparison_usage (first second : SignedWord) (W : ℕ) (hA : width first ≤ W) (hB : width second ≤ W) :
    usage (BinaryQuadraticExpressionLifetime.compareWithTrace first second).2 ≤ comparisonEnvelope W := by
  have h := BinaryQuadraticExpressionLifetime.compareWithTrace_bounds first second W hA hB
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells comparisonEnvelope
  omega

def andThenWithTrace (first : Bool × Trace) (later : Unit → Bool × Trace) : Bool × Trace :=
  if first.1 then
    let next := later ()
    (next.1,wrap 16 2 [first.2,next.2])
  else (false,wrap 8 2 [first.2])

theorem andThenWithTrace_state (first : Bool × Trace) (later : Unit → Bool × Trace) :
    (andThenWithTrace first later).1 = (first.1 && (later ()).1) := by
  unfold andThenWithTrace
  cases first.1 <;> rfl

theorem andThenWithTrace_usage (first : Bool × Trace) (later : Unit → Bool × Trace) (A B : ℕ)
    (hA : usage first.2 ≤ A) (hB : usage (later ()).2 ≤ B) :
    usage (andThenWithTrace first later).2 ≤ A+B+64 := by
  unfold andThenWithTrace
  split
  · have hw := wrap_usage 16 2 [first.2,(later ()).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [first.2,(later ()).2]) ≤ _
    omega
  · have hw := wrap_usage 8 2 [first.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 8 2 [first.2]) ≤ _
    omega

def positiveWithTrace (word : SignedWord) : Bool × Trace :=
  let compared := BinaryQuadraticExpressionLifetime.compareWithTrace word zero
  (!compared.1,wrap 8 1 [compared.2])

theorem positiveWithTrace_state (word : SignedWord) :
    (positiveWithTrace word).1 = BinaryPRGRecognition.positive word := by
  simp only [positiveWithTrace,BinaryQuadraticExpressionLifetime.compareWithTrace_erases,BinaryPRGRecognition.positive]

theorem positiveWithTrace_usage (word : SignedWord) (W : ℕ) (hWord : width word ≤ W) (hZero : width zero ≤ W) :
    usage (positiveWithTrace word).2 ≤ comparisonEnvelope W+64 := by
  have h := comparison_usage word zero W hWord hZero
  have hw := wrap_usage 8 1 [(BinaryQuadraticExpressionLifetime.compareWithTrace word zero).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (positiveWithTrace word).2 ≤ _ at hw
  omega

def equalWithTrace (first second : SignedWord) : Bool × Trace :=
  andThenWithTrace (BinaryQuadraticExpressionLifetime.compareWithTrace first second)
    (fun _ => BinaryQuadraticExpressionLifetime.compareWithTrace second first)

theorem equalWithTrace_state (first second : SignedWord) :
    (equalWithTrace first second).1 = BinaryPRGRecognition.equal first second := by
  simp only [equalWithTrace,andThenWithTrace_state,BinaryQuadraticExpressionLifetime.compareWithTrace_erases,BinaryPRGRecognition.equal]

theorem equalWithTrace_usage (first second : SignedWord) (W : ℕ) (hA : width first ≤ W) (hB : width second ≤ W) :
    usage (equalWithTrace first second).2 ≤ 2*comparisonEnvelope W+64 := by
  have h := andThenWithTrace_usage (BinaryQuadraticExpressionLifetime.compareWithTrace first second)
    (fun _ => BinaryQuadraticExpressionLifetime.compareWithTrace second first) _ _
    (comparison_usage first second W hA hB) (comparison_usage second first W hB hA)
  change usage (equalWithTrace first second).2 ≤ _ at h
  omega

def allWithTrace (f : SignedWord → Bool × Trace) : List SignedWord → Bool × Trace
  | [] => (true,wrap 8 1 [])
  | word::rest => andThenWithTrace (f word) (fun _ => allWithTrace f rest)

theorem allWithTrace_state (f : SignedWord → Bool × Trace) (words : List SignedWord) :
    (allWithTrace f words).1 = words.all (fun word => (f word).1) := by
  induction words with
  | nil => rfl
  | cons word rest ih => simp only [allWithTrace,andThenWithTrace_state,ih,List.all_cons]

theorem allWithTrace_usage (f : SignedWord → Bool × Trace) (words : List SignedWord) (P : ℕ)
    (h : ∀ word ∈ words,usage (f word).2 ≤ P) :
    usage (allWithTrace f words).2 ≤ words.length*(P+64)+64 := by
  induction words with
  | nil => exact (wrap_usage 8 1 []).trans (by simp)
  | cons word rest ih =>
      have ht := ih (fun item hi => h item (by simp [hi]))
      have hw := andThenWithTrace_usage (f word) (fun _ => allWithTrace f rest) P _ (h word (by simp)) ht
      change usage (allWithTrace f (word::rest)).2 ≤ _ at hw
      simp only [List.length_cons,Nat.add_mul,one_mul]
      omega

def scaledWithTrace (twice b word : SignedWord) : Bool × Trace :=
  let scaled := BinaryQuadraticLifetime.applyWithTrace .mul twice word
  let compared := BinaryQuadraticExpressionLifetime.compareWithTrace scaled.1 b
  (compared.1,wrap 24 2 [scaled.2,compared.2])

theorem scaledWithTrace_state (twice b word : SignedWord) (hT : Valid twice) (hW : Valid word) :
    (scaledWithTrace twice b word).1 = BinaryRationalArithmetic.lessEqual (apply .mul twice word) b := by
  simp only [scaledWithTrace,BinaryQuadraticExpressionLifetime.compareWithTrace_erases,
    BinaryQuadraticLifetime.applyWithTrace_state .mul twice word hT hW]

theorem scaledWithTrace_usage (twice b word : SignedWord) (hT : Valid twice) (hV : Valid word) (W : ℕ)
    (hTwice : width twice ≤ W) (hB : width b ≤ W) (hWord : width word ≤ W)
    (hScaled : width (apply .mul twice word) ≤ W) :
    usage (scaledWithTrace twice b word).2 ≤ opcodeEnvelope W+comparisonEnvelope W+64 := by
  have hOp := opcode_usage .mul twice word W hTwice hWord
  have hBound : width (BinaryQuadraticLifetime.applyWithTrace .mul twice word).1 ≤ W := by
    rw [BinaryQuadraticLifetime.applyWithTrace_state .mul twice word hT hV]
    exact hScaled
  have hCmp := comparison_usage (BinaryQuadraticLifetime.applyWithTrace .mul twice word).1 b W hBound hB
  have hw := wrap_usage 24 2 [(BinaryQuadraticLifetime.applyWithTrace .mul twice word).2,
    (BinaryQuadraticExpressionLifetime.compareWithTrace (BinaryQuadraticLifetime.applyWithTrace .mul twice word).1 b).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (scaledWithTrace twice b word).2 ≤ _ at hw
  omega

end Blotto.BinaryPRGPromiseControlLifetime
