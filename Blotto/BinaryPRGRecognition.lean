import Blotto.BinaryExpressionCompiler
import Blotto.RationalPRGRecognition

/-! Numerical PRG recognition operates on stored Boolean rational words.
Denominator validity/canonicality is supplied by the separately verified frame
parser. The promise guard itself uses Boolean arithmetic, comparisons and a
stored-word sum. Its certified result keeps the original words; a rational
source is constructed only in proofs. Rejection is failure of this ordered
PRG promise, not a claim about existence in the general game. -/

namespace Blotto.BinaryPRGRecognition
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open scoped BigOperators

structure Input (n : ℕ) where
  a : SignedWord
  b : SignedWord
  values : FixedArrayTable n SignedWord

def Input.Canonical {n : ℕ} (input : Input n) : Prop :=
  CanonicalWord input.a ∧ CanonicalWord input.b ∧ ∀ j, CanonicalWord (input.values.read j)

def Input.Checks {n : ℕ} (input : Input n) : Prop :=
  RationalPRGChecks (fun j => value (input.values.read j)) (value input.a) (value input.b)

def one : SignedWord := BinaryExpressionCompiler.Constant.one.word
def two : SignedWord := BinaryExpressionCompiler.Constant.two.word

theorem one_value : value one = 1 := BinaryExpressionCompiler.Constant.word_value .one
theorem two_value : value two = 2 := BinaryExpressionCompiler.Constant.word_value .two
theorem one_canonical : CanonicalWord one := BinaryExpressionCompiler.Constant.word_canonical .one
theorem two_canonical : CanonicalWord two := BinaryExpressionCompiler.Constant.word_canonical .two

theorem opcode_canonical (op : RealArithmeticOp) (a b : SignedWord)
    (ha : CanonicalWord a) (hb : CanonicalWord b) : CanonicalWord (apply op a b) := by
  refine ⟨apply_valid op a b ha.1 hb.1, ?_⟩
  have h := apply_width op a b ha.1 hb.1
  rw [← apply_value op a b ha.1 hb.1] at h
  exact h

def sumWords : List SignedWord → SignedWord
  | [] => zero
  | word :: rest => apply .add word (sumWords rest)

theorem sumWords_canonical (words : List SignedWord)
    (h : ∀ word ∈ words, CanonicalWord word) : CanonicalWord (sumWords words) := by
  induction words with
  | nil => exact zero_canonical
  | cons word rest ih =>
      exact opcode_canonical .add _ _ (h word (by simp))
        (ih (fun w hw => h w (by simp [hw])))

theorem sumWords_value (words : List SignedWord)
    (h : ∀ word ∈ words, CanonicalWord word) :
    value (sumWords words) = (words.map value).sum := by
  induction words with
  | nil => exact zero_value
  | cons word rest ih =>
      have ht : ∀ w ∈ rest, CanonicalWord w := fun w hw => h w (by simp [hw])
      rw [sumWords, apply_value .add _ _ (h word (by simp)).1 (sumWords_canonical rest ht).1]
      simpa only [RealArithmeticOp.applyRat, List.map_cons, List.sum_cons] using
        congrArg (fun q => value word + q) (ih ht)

def positive (word : SignedWord) : Bool := !BinaryRationalArithmetic.lessEqual word zero
def equal (first second : SignedWord) : Bool :=
  BinaryRationalArithmetic.lessEqual first second && BinaryRationalArithmetic.lessEqual second first

theorem positive_iff (word : SignedWord) (h : CanonicalWord word) :
    positive word = true ↔ 0 < value word := by
  have hl := BinaryRationalArithmetic.lessEqual_iff word zero h.1 zero_valid
  rw [zero_value] at hl
  simpa [positive] using not_congr hl

theorem equal_iff (first second : SignedWord) (hA : CanonicalWord first) (hB : CanonicalWord second) :
    equal first second = true ↔ value first = value second := by
  rw [equal, Bool.and_eq_true, BinaryRationalArithmetic.lessEqual_iff _ _ hA.1 hB.1,
    BinaryRationalArithmetic.lessEqual_iff _ _ hB.1 hA.1]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

def scaledField (a word : SignedWord) : SignedWord := apply .mul (apply .mul two a) word

theorem scaledField_canonical (a word : SignedWord) (ha : CanonicalWord a) (hw : CanonicalWord word) :
    CanonicalWord (scaledField a word) :=
  opcode_canonical .mul _ _ (opcode_canonical .mul _ _ two_canonical ha) hw

theorem scaledField_value (a word : SignedWord) (ha : CanonicalWord a) (hw : CanonicalWord word) :
    value (scaledField a word) = 2 * value a * value word := by
  rw [scaledField, apply_value .mul _ _ (opcode_canonical .mul _ _ two_canonical ha).1 hw.1,
    apply_value .mul _ _ two_canonical.1 ha.1, two_value]
  rfl

def checkBool {n : ℕ} (input : Input n) : Bool :=
  let row := List.ofFn input.values.read
  row.all positive && equal (sumWords row) one && positive input.a && positive input.b &&
    BinaryRationalArithmetic.lessEqual input.b input.a &&
      row.all (fun word => BinaryRationalArithmetic.lessEqual (scaledField input.a word) input.b)

theorem checkBool_iff {n : ℕ} (input : Input n) (h : input.Canonical) :
    checkBool input = true ↔ input.Checks := by
  have hr : ∀ word ∈ List.ofFn input.values.read, CanonicalWord word := by
    intro word hw
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
    exact h.2.2 j
  have hp : ∀ j, positive (input.values.read j) = true ↔ 0 < value (input.values.read j) :=
    fun j => positive_iff _ (h.2.2 j)
  have hs : equal (sumWords (List.ofFn input.values.read)) one = true ↔
      (∑ j, value (input.values.read j)) = 1 := by
    rw [equal_iff _ _ (sumWords_canonical _ hr) one_canonical, sumWords_value _ hr,
      List.map_ofFn, List.sum_ofFn, one_value]
    rfl
  have hf : ∀ j,
      BinaryRationalArithmetic.lessEqual (scaledField input.a (input.values.read j)) input.b = true ↔
        2 * value input.a * value (input.values.read j) ≤ value input.b := by
    intro j
    rw [BinaryRationalArithmetic.lessEqual_iff _ _
      (scaledField_canonical _ _ h.1 (h.2.2 j)).1 h.2.1.1,
      scaledField_value _ _ h.1 (h.2.2 j)]
  simp only [checkBool, Bool.and_eq_true, List.all_eq_true, List.mem_ofFn, forall_exists_index,
    forall_apply_eq_imp_iff, hs, hp, hf, positive_iff _ h.1, positive_iff _ h.2.1,
    BinaryRationalArithmetic.lessEqual_iff _ _ h.2.1.1 h.1.1, Input.Checks, RationalPRGChecks, and_assoc]

def recognize {n : ℕ} (input : Input n) (hC : input.Canonical) : Option {i : Input n // i.Checks} :=
  if h : checkBool input = true then some ⟨input, (checkBool_iff input hC).mp h⟩ else none

theorem recognize_isSome {n : ℕ} (input : Input n) (hC : input.Canonical) :
    (recognize input hC).isSome = true ↔ input.Checks := by
  by_cases hb : checkBool input = true
  · have hi := (checkBool_iff input hC).mp hb
    simp [recognize, hb, hi]
  · have hi : ¬input.Checks := fun hi => hb ((checkBool_iff input hC).mpr hi)
    simp [recognize, hb, hi]

theorem recognize_none {n : ℕ} (input : Input n) (hC : input.Canonical) :
    recognize input hC = none ↔ ¬input.Checks := by
  by_cases hb : checkBool input = true
  · have hi := (checkBool_iff input hC).mp hb
    simp [recognize, hb, hi]
  · have hi : ¬input.Checks := fun hi => hb ((checkBool_iff input hC).mpr hi)
    simp [recognize, hb, hi]

theorem recognize_data {n : ℕ} (input : Input n) (hC : input.Canonical)
    (result : {i : Input n // i.Checks}) (h : recognize input hC = some result) : result.val = input := by
  unfold recognize at h
  split at h
  · cases Option.some.inj h
    rfl
  · cases h

noncomputable def Input.source {n : ℕ} (input : Input n) (h : input.Checks) : RationalPRGOriginalInput n :=
  ⟨fun j => value (input.values.read j), h.1, h.2.1, value input.a, value input.b,
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end Blotto.BinaryPRGRecognition
