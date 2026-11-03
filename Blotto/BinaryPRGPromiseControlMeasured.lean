import Blotto.BinaryQuadraticExpressionMeasured
import Blotto.BinaryPRGPromiseControlLifetime

/-! Actual reached comparisons/arithmetic and delayed guards return old
data/trace and source work together. Failed guards never execute their
continuations. Width prices concern actual Boolean/list backends, not the
older Euclidean checker or storage envelopes. Native model joins remain. -/
namespace Blotto.BinaryPRGPromiseControlMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryPRGRecognition
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false

def andThen (first : (Bool × Trace) × ℕ) (later : Unit → (Bool × Trace) × ℕ) : (Bool × Trace) × ℕ :=
  if first.1.1 then
    let next := later ()
    ((next.1.1,wrap 16 2 [first.1.2,next.1.2]),first.2+next.2+4)
  else ((false,wrap 8 2 [first.1.2]),first.2+4)

theorem andThen_erases (first : (Bool × Trace) × ℕ) (later : Unit → (Bool × Trace) × ℕ) :
    (andThen first later).1 = BinaryPRGPromiseControlLifetime.andThenWithTrace first.1 (fun u => (later u).1) := by
  unfold andThen BinaryPRGPromiseControlLifetime.andThenWithTrace
  cases first.1.1 <;> rfl

theorem andThen_reject (first : (Bool × Trace) × ℕ) (later : Unit → (Bool × Trace) × ℕ)
    (h : first.1.1 = false) :
    andThen first later = ((false,wrap 8 2 [first.1.2]),first.2+4) := by simp only [andThen,h,Bool.false_eq_true,ite_false]

theorem andThen_work (first : (Bool × Trace) × ℕ) (later : Unit → (Bool × Trace) × ℕ) (A B : ℕ)
    (hA : first.2 ≤ A) (hB : (later ()).2 ≤ B) : (andThen first later).2 ≤ A+B+4 := by
  unfold andThen
  split <;> dsimp only <;> omega

def positive (word : SignedWord) : (Bool × Trace) × ℕ :=
  let compared := BinaryQuadraticExpressionMeasured.compare word zero
  ((!compared.1.1,wrap 8 1 [compared.1.2]),compared.2+4)

theorem positive_erases (word : SignedWord) : (positive word).1 = BinaryPRGPromiseControlLifetime.positiveWithTrace word := by
  simp only [positive,BinaryPRGPromiseControlLifetime.positiveWithTrace,BinaryQuadraticExpressionMeasured.compare_erases]

def equal (first second : SignedWord) : (Bool × Trace) × ℕ :=
  andThen (BinaryQuadraticExpressionMeasured.compare first second)
    (fun _ => BinaryQuadraticExpressionMeasured.compare second first)

theorem equal_erases (first second : SignedWord) :
    (equal first second).1 = BinaryPRGPromiseControlLifetime.equalWithTrace first second := by
  simp only [equal,BinaryPRGPromiseControlLifetime.equalWithTrace,andThen_erases,
    BinaryQuadraticExpressionMeasured.compare_erases]

def all (f : SignedWord → (Bool × Trace) × ℕ) : List SignedWord → (Bool × Trace) × ℕ
  | [] => ((true,wrap 8 1 []),4)
  | word::rest => andThen (f word) (fun _ => all f rest)

theorem all_erases (f : SignedWord → (Bool × Trace) × ℕ) (words : List SignedWord) :
    (all f words).1 = BinaryPRGPromiseControlLifetime.allWithTrace (fun word => (f word).1) words := by
  induction words with
  | nil => rfl
  | cons word rest ih => simp only [all,BinaryPRGPromiseControlLifetime.allWithTrace,andThen_erases,ih]

theorem all_work (f : SignedWord → (Bool × Trace) × ℕ) (words : List SignedWord) (P : ℕ)
    (h : ∀ word ∈ words,(f word).2 ≤ P) : (all f words).2 ≤ words.length*(P+4)+4 := by
  induction words with
  | nil => simp [all]
  | cons word rest ih =>
      have ht := ih (fun item hi => h item (by simp [hi]))
      have hw := andThen_work (f word) (fun _ => all f rest) P _ (h word (by simp)) ht
      change (all f (word::rest)).2 ≤ _ at hw
      simp only [List.length_cons,Nat.add_mul,one_mul]
      omega

def scaled (twice b word : SignedWord) : (Bool × Trace) × ℕ :=
  let scaled := BinaryQuadraticMeasured.apply .mul twice word
  let compared := BinaryQuadraticExpressionMeasured.compare scaled.1.1 b
  ((compared.1.1,wrap 24 2 [scaled.1.2,compared.1.2]),scaled.2+compared.2+8)

theorem scaled_erases (twice b word : SignedWord) :
    (scaled twice b word).1 = BinaryPRGPromiseControlLifetime.scaledWithTrace twice b word := by
  simp only [scaled,BinaryPRGPromiseControlLifetime.scaledWithTrace,
    BinaryQuadraticMeasured.apply_erases,BinaryQuadraticExpressionMeasured.compare_erases]

def opcodePrice (W : ℕ) : ℕ := 11000*(W+1)^2
def comparisonPrice (W : ℕ) : ℕ := BinaryQuadraticExpression.uniformPrice W

theorem opcode_bound (op : RealArithmeticOp) (first second : SignedWord) (W : ℕ)
    (hA : width first ≤ W) (hB : width second ≤ W) :
    (BinaryQuadraticMeasured.apply op first second).2 ≤ opcodePrice W := by
  have hPair : BinaryRationalArithmetic.pairWidth first second ≤ W := by
    unfold BinaryRationalArithmetic.pairWidth
    omega
  exact (BinaryQuadraticMeasured.apply_bound op first second).trans
    (Nat.mul_le_mul_left 11000 (Nat.pow_le_pow_left (Nat.add_le_add_right hPair 1) 2))

theorem comparison_bound (first second : SignedWord) (W : ℕ)
    (hA : width first ≤ W) (hB : width second ≤ W) :
    (BinaryQuadraticExpressionMeasured.compare first second).2 ≤ comparisonPrice W := by
  rw [BinaryQuadraticExpressionMeasured.compare_work]
  exact BinaryQuadraticExpression.comparePrice_bound first second W (by omega) (by omega)

theorem positive_work (word : SignedWord) (W : ℕ) (hWord : width word ≤ W) (hZero : width zero ≤ W) :
    (positive word).2 ≤ comparisonPrice W+4 := by
  exact Nat.add_le_add_right (comparison_bound word zero W hWord hZero) 4

theorem equal_work (first second : SignedWord) (W : ℕ) (hA : width first ≤ W) (hB : width second ≤ W) :
    (equal first second).2 ≤ 2*comparisonPrice W+4 := by
  have h := andThen_work (BinaryQuadraticExpressionMeasured.compare first second)
    (fun _ => BinaryQuadraticExpressionMeasured.compare second first) _ _
    (comparison_bound first second W hA hB) (comparison_bound second first W hB hA)
  change (equal first second).2 ≤ _ at h
  omega

theorem scaled_work (twice b word : SignedWord) (hT : Valid twice) (hV : Valid word) (W : ℕ)
    (hTwice : width twice ≤ W) (hB : width b ≤ W) (hWord : width word ≤ W)
    (hScaled : width (apply .mul twice word) ≤ W) :
    (scaled twice b word).2 ≤ opcodePrice W+comparisonPrice W+8 := by
  have hOp := opcode_bound .mul twice word W hTwice hWord
  have hActual : width (BinaryQuadraticMeasured.apply .mul twice word).1.1 ≤ W := by
    rw [BinaryQuadraticMeasured.apply_erases,BinaryQuadraticLifetime.applyWithTrace_state .mul twice word hT hV]
    exact hScaled
  have hCmp := comparison_bound (BinaryQuadraticMeasured.apply .mul twice word).1.1 b W hActual hB
  change (BinaryQuadraticMeasured.apply .mul twice word).2+
    (BinaryQuadraticExpressionMeasured.compare (BinaryQuadraticMeasured.apply .mul twice word).1.1 b).2+8 ≤ _
  omega

end Blotto.BinaryPRGPromiseControlMeasured
