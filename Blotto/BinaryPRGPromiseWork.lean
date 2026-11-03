import Blotto.BinaryStoredWordSumWork

/-! Actual ordered PRG promise checking retains all reached comparison and
arithmetic results and shares one doubled rich budget for field tests.
Arbitrary canonical decoded words derive the complete recorded primitive
bound, including rejection and short-circuiting. Parsing/control/copy and
physical execution/storage remain separate. -/

namespace Blotto.BinaryPRGPromiseWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryPRGRecognition
open BinaryStoredWordSumWork BinaryPRGPreparationWork
open scoped BigOperators

def compareWithWork (first second : SignedWord) : Bool × ℕ :=
  (BinaryRationalArithmetic.lessEqual first second,BinaryRationalArithmetic.lessEqualWork first second)

def positiveWithWork (word : SignedWord) : Bool × ℕ :=
  let compared := compareWithWork word zero
  (!compared.1,compared.2)

def andThen (first : Bool × ℕ) (later : Unit → Bool × ℕ) : Bool × ℕ :=
  if first.1 then let next := later (); (next.1,first.2 + next.2) else (false,first.2)

theorem andThen_state (first : Bool × ℕ) (later : Unit → Bool × ℕ) :
    (andThen first later).1 = (first.1 && (later ()).1) := by
  rcases first with ⟨flag,work⟩
  cases flag <;> rfl

theorem andThen_bound (first : Bool × ℕ) (later : Unit → Bool × ℕ) (A B : ℕ)
    (hA : first.2 ≤ A) (hB : (later ()).2 ≤ B) : (andThen first later).2 ≤ A + B := by
  unfold andThen
  split <;> dsimp only <;> omega

def allWithWork (f : SignedWord → Bool × ℕ) : List SignedWord → Bool × ℕ
  | [] => (true,0)
  | word :: rest => andThen (f word) (fun _ => allWithWork f rest)

theorem allWithWork_state (f : SignedWord → Bool × ℕ) (words : List SignedWord) :
    (allWithWork f words).1 = words.all (fun word => (f word).1) := by
  induction words with
  | nil => rfl
  | cons word rest ih => rw [allWithWork,andThen_state,ih]; rfl

theorem allWithWork_bound (f : SignedWord → Bool × ℕ) (words : List SignedWord) (P : ℕ)
    (h : ∀ word ∈ words, (f word).2 ≤ P) : (allWithWork f words).2 ≤ words.length * P := by
  induction words with
  | nil => exact Nat.zero_le _
  | cons word rest ih =>
      have ht := ih (fun item hi => h item (by simp [hi]))
      exact (andThen_bound (f word) (fun _ => allWithWork f rest) P (rest.length * P) (h word (by simp)) ht).trans_eq (by simp only [List.length_cons]; ring)

def equalWithWork (first second : SignedWord) : Bool × ℕ :=
  andThen (compareWithWork first second) (fun _ => compareWithWork second first)

theorem equalWithWork_state (first second : SignedWord) : (equalWithWork first second).1 = equal first second := by
  rw [equalWithWork,andThen_state]; rfl

def scaledWithWork (twice b word : SignedWord) : Bool × ℕ :=
  let scaled := applyWithWork .mul twice word
  let compared := compareWithWork scaled.1 b
  (compared.1,scaled.2 + compared.2)

def fieldsWithWork {n : ℕ} (input : Input n) (row : List SignedWord) : Bool × ℕ :=
  let twice := applyWithWork .mul two input.a
  let fields := allWithWork (scaledWithWork twice.1 input.b) row
  (fields.1,twice.2 + fields.2)

def remainingWithWork {n : ℕ} (input : Input n) (row : List SignedWord) : Bool × ℕ :=
  let summed := sumWithWork row
  let later := andThen (equalWithWork summed.1 one) (fun _ =>
    andThen (positiveWithWork input.a) (fun _ =>
      andThen (positiveWithWork input.b) (fun _ =>
        andThen (compareWithWork input.b input.a) (fun _ => fieldsWithWork input row))))
  (later.1,summed.2 + later.2)

def checkWithWork {n : ℕ} (input : Input n) : Bool × ℕ :=
  let row := List.ofFn input.values.read
  andThen (allWithWork positiveWithWork row) (fun _ => remainingWithWork input row)

theorem fieldsWithWork_state {n : ℕ} (input : Input n) (row : List SignedWord) :
    (fieldsWithWork input row).1 = row.all (fun word => BinaryRationalArithmetic.lessEqual (scaledField input.a word) input.b) := by
  unfold fieldsWithWork
  rw [allWithWork_state]
  rfl

theorem remainingWithWork_state {n : ℕ} (input : Input n) (row : List SignedWord) :
    (remainingWithWork input row).1 = (equal (sumWords row) one && positive input.a && positive input.b &&
      BinaryRationalArithmetic.lessEqual input.b input.a && row.all (fun word => BinaryRationalArithmetic.lessEqual (scaledField input.a word) input.b)) := by
  unfold remainingWithWork
  simp only [sumWithWork_state,andThen_state,equalWithWork_state,fieldsWithWork_state]
  simp only [positiveWithWork,compareWithWork,positive,Bool.and_assoc]

theorem checkWithWork_state {n : ℕ} (input : Input n) : (checkWithWork input).1 = checkBool input := by
  unfold checkWithWork checkBool
  rw [andThen_state,allWithWork_state,remainingWithWork_state]
  simp only [positiveWithWork,compareWithWork,positive,Bool.and_assoc]
  rfl

def heightCredit {n : ℕ} (input : Input n) : ℕ := storedInputWidth input + n + 3
def operandWidth {n : ℕ} (input : Input n) : ℕ := 12 * heightCredit input + 10
def operationPrice (W : ℕ) : ℕ := 12000 * (W + 1) ^ 3
def comparisonPrice (W : ℕ) : ℕ := 500 * (W + 1) ^ 2

theorem compareWithWork_bound (first second : SignedWord) (W : ℕ) (hA : width first ≤ W) (hB : width second ≤ W) :
    (compareWithWork first second).2 ≤ comparisonPrice W :=
  (BinaryRationalArithmetic.lessEqualWork_bound first second).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le hA hB) 1) 2))

theorem input_widths {n : ℕ} (input : Input n) : width input.a ≤ operandWidth input ∧ width input.b ≤ operandWidth input ∧
    (∀ j, width (input.values.read j) ≤ operandWidth input) ∧ width one ≤ operandWidth input ∧ width two ≤ operandWidth input ∧ width zero ≤ operandWidth input := by
  have h := original_widths input
  have hm : storedInputWidth input ≤ operandWidth input := by unfold operandWidth heightCredit; omega
  refine ⟨h.1.trans hm,h.2.1.trans hm,fun j => (h.2.2.1 j).trans hm,?_,?_,?_⟩
  · change 1 ≤ operandWidth input; unfold operandWidth heightCredit; omega
  · change 2 ≤ operandWidth input; unfold operandWidth heightCredit; omega
  · change 1 ≤ operandWidth input; unfold operandWidth heightCredit; omega

theorem row_credit {n : ℕ} (input : Input n) : credit (List.ofFn input.values.read) ≤ heightCredit input := by
  simp only [credit,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_fin,Nat.nsmul_eq_mul,mul_one]
  unfold heightCredit storedInputWidth
  omega

theorem sum_width {n : ℕ} (input : Input n) (hC : input.Canonical) :
    width (sumWords (List.ofFn input.values.read)) ≤ operandWidth input := by
  have hc : ∀ word ∈ List.ofFn input.values.read, CanonicalWord word := by
    intro word hw; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw; exact hC.2.2 j
  have h := (sumWords_canonical _ hc).2.trans (rationalWordWidth_of_height (sum_height _ hc))
  have hm := row_credit input
  unfold operandWidth heightCredit at *
  omega

theorem twice_width {n : ℕ} (input : Input n) : width (apply .mul two input.a) ≤ 3 * storedInputWidth input + 1 := by
  have h := original_widths input
  exact (apply_stored_width .mul two input.a).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (max_le (by change 2 ≤ storedInputWidth input; exact h.2.2.2) h.1)) 1)

theorem scaled_width {n : ℕ} (input : Input n) (j : Fin n) :
    width (scaledField input.a (input.values.read j)) ≤ operandWidth input := by
  have h := original_widths input
  have ht := twice_width input
  have hp := apply_stored_width .mul (apply .mul two input.a) (input.values.read j)
  have hm : max (width (apply .mul two input.a)) (width (input.values.read j)) ≤ 3 * storedInputWidth input + 1 :=
    max_le ht ((h.2.2.1 j).trans (by omega))
  have he := hp.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hm) 1)
  change width (scaledField input.a (input.values.read j)) ≤ _ at he
  unfold operandWidth heightCredit
  omega

def bound {n : ℕ} (input : Input n) : ℕ := (2 * n + 1) * operationPrice (operandWidth input) +
  (2 * n + 5) * comparisonPrice (operandWidth input)

theorem checkWithWork_bound {n : ℕ} (input : Input n) (hC : input.Canonical) : (checkWithWork input).2 ≤ bound input := by
  let row := List.ofFn input.values.read
  let W := operandWidth input
  let P := operationPrice W
  let C := comparisonPrice W
  have hw := input_widths input
  have hc : ∀ word ∈ row, CanonicalWord word := by intro word h; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h; exact hC.2.2 j
  have hPos : ∀ word ∈ row, (positiveWithWork word).2 ≤ C := by
    intro word h; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
    exact compareWithWork_bound _ _ W (hw.2.2.1 j) hw.2.2.2.2.2
  have hAll := allWithWork_bound positiveWithWork row C hPos
  have hSum := sumWithWork_bound row hc
  have hCredit := row_credit input
  have hPrice : 12000 * (2 * credit row + 2) ^ 3 ≤ P := by
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    dsimp [P,operationPrice,W,operandWidth,heightCredit]
    change credit row ≤ heightCredit input at hCredit
    unfold heightCredit at hCredit
    omega
  have hSum' := hSum.trans (Nat.mul_le_mul_left row.length hPrice)
  have hSumWidth := sum_width input hC
  have hEq := andThen_bound (compareWithWork (sumWithWork row).1 one) (fun _ => compareWithWork one (sumWithWork row).1)
    C C (by rw [sumWithWork_state]; exact compareWithWork_bound _ _ W hSumWidth hw.2.2.2.1)
    (by rw [sumWithWork_state]; exact compareWithWork_bound _ _ W hw.2.2.2.1 hSumWidth)
  have hA := compareWithWork_bound input.a zero W hw.1 hw.2.2.2.2.2
  have hB := compareWithWork_bound input.b zero W hw.2.1 hw.2.2.2.2.2
  have hOrder := compareWithWork_bound input.b input.a W hw.2.1 hw.1
  have ht := twice_width input
  have htW : width (apply .mul two input.a) ≤ W := by dsimp [W,operandWidth,heightCredit]; omega
  have hTwice := operation_uniform_bound .mul two input.a W hw.2.2.2.2.1 hw.1
  have hScaled : ∀ word ∈ row, (scaledWithWork (apply .mul two input.a) input.b word).2 ≤ P + C := by
    intro word h; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
    have hp := operation_uniform_bound .mul (apply .mul two input.a) (input.values.read j) W htW (hw.2.2.1 j)
    have hq := compareWithWork_bound (scaledField input.a (input.values.read j)) input.b W (scaled_width input j) hw.2.1
    exact Nat.add_le_add hp hq
  have hFields := allWithWork_bound (scaledWithWork (apply .mul two input.a) input.b) row (P + C) hScaled
  have hFieldsFull : (fieldsWithWork input row).2 ≤ P + row.length * (P + C) := by
    unfold fieldsWithWork
    dsimp only
    rw [applyWithWork_state]
    exact Nat.add_le_add hTwice hFields
  have hChecks := andThen_bound (compareWithWork input.b input.a) (fun _ => fieldsWithWork input row) C _ hOrder hFieldsFull
  have hBudgetB := andThen_bound (positiveWithWork input.b) (fun _ => andThen (compareWithWork input.b input.a) (fun _ => fieldsWithWork input row)) C _ hB hChecks
  have hBudgetA := andThen_bound (positiveWithWork input.a) (fun _ => andThen (positiveWithWork input.b) (fun _ => andThen (compareWithWork input.b input.a) (fun _ => fieldsWithWork input row))) C _ hA hBudgetB
  have hEqual := andThen_bound (equalWithWork (sumWithWork row).1 one) (fun _ => andThen (positiveWithWork input.a) (fun _ => andThen (positiveWithWork input.b) (fun _ => andThen (compareWithWork input.b input.a) (fun _ => fieldsWithWork input row)))) (C + C) _ hEq hBudgetA
  have hRest : (remainingWithWork input row).2 ≤ row.length * P + (C + C + (C + (C + (C + (P + row.length * (P + C)))))) :=
    Nat.add_le_add hSum' hEqual
  have hTotal := andThen_bound (allWithWork positiveWithWork row) (fun _ => remainingWithWork input row) (row.length * C) _ hAll hRest
  change (checkWithWork input).2 ≤ _ at hTotal
  dsimp only [row] at hTotal
  simp only [List.length_ofFn] at hTotal
  exact hTotal.trans_eq (by unfold bound; dsimp [P,C,W]; ring)

end Blotto.BinaryPRGPromiseWork
