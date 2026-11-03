import Blotto.BinaryStoredWordSumLifetime

/-! Complete ordered PRG promise execution. One supplied value row feeds early
positivity, tail-to-head sum/equality, budget tests and the final field tests.
The doubled rich budget is produced once and shared. Reached original-word
credits derive every operand width on accepted and rejected canonical games.
The selected checked-game path supplies the row retained by framing; the
original array-projection checker remains as an exact reference. -/
namespace Blotto.BinaryPRGPromiseLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryPRGRecognition
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryLifetimeUsage
open BinaryPRGPromiseControlLifetime
set_option maxHeartbeats 3000000

def fieldsWithTrace {n : ℕ} (input : Input n) (row : List SignedWord) : Bool × Trace :=
  let twice := BinaryQuadraticLifetime.applyWithTrace .mul two input.a
  let fields := allWithTrace (scaledWithTrace twice.1 input.b) row
  (fields.1,wrap 24 2 [twice.2,fields.2])

theorem fieldsWithTrace_state {n : ℕ} (input : Input n) (hC : input.Canonical) (row : List SignedWord)
    (hRow : ∀ word ∈ row,CanonicalWord word) :
    (fieldsWithTrace input row).1 = (BinaryPRGPromiseWork.fieldsWithWork input row).1 := by
  rw [BinaryPRGPromiseWork.fieldsWithWork_state]
  unfold fieldsWithTrace
  dsimp only
  rw [allWithTrace_state,BinaryQuadraticLifetime.applyWithTrace_state .mul two input.a two_canonical.1 hC.1.1]
  have hAll : ∀ words : List SignedWord,(∀ word ∈ words,CanonicalWord word) →
      words.all (fun word => (scaledWithTrace (apply .mul two input.a) input.b word).1) =
        words.all (fun word => BinaryRationalArithmetic.lessEqual (scaledField input.a word) input.b) := by
    intro words
    induction words with
    | nil => intro _; rfl
    | cons word rest ih =>
        intro hc
        have ht : ∀ item ∈ rest,CanonicalWord item := fun item hi => hc item (by simp [hi])
        have hh := scaledWithTrace_state (apply .mul two input.a) input.b word
          (apply_valid .mul two input.a two_canonical.1 hC.1.1) (hc word (by simp)).1
        exact congrArg₂ (fun a b : Bool => a && b) hh (ih ht)
  exact hAll row hRow

def remainingWithTrace {n : ℕ} (input : Input n) (row : List SignedWord) : Bool × Trace :=
  let summed := BinaryStoredWordSumLifetime.sumWithTrace row
  let later := andThenWithTrace (equalWithTrace summed.1 one) (fun _ =>
    andThenWithTrace (positiveWithTrace input.a) (fun _ =>
      andThenWithTrace (positiveWithTrace input.b) (fun _ =>
        andThenWithTrace (BinaryQuadraticExpressionLifetime.compareWithTrace input.b input.a)
          (fun _ => fieldsWithTrace input row))))
  (later.1,wrap 24 2 [summed.2,later.2])

theorem remainingWithTrace_state {n : ℕ} (input : Input n) (hC : input.Canonical) (row : List SignedWord)
    (hRow : ∀ word ∈ row,CanonicalWord word) :
    (remainingWithTrace input row).1 = (BinaryPRGPromiseWork.remainingWithWork input row).1 := by
  rw [BinaryPRGPromiseWork.remainingWithWork_state]
  simp only [remainingWithTrace,andThenWithTrace_state,equalWithTrace_state,positiveWithTrace_state,
    BinaryStoredWordSumLifetime.sumWithTrace_state row hRow,
    BinaryQuadraticExpressionLifetime.compareWithTrace_erases,fieldsWithTrace_state input hC row hRow,
    BinaryPRGPromiseWork.fieldsWithWork_state,Bool.and_assoc]

def checkWithTrace {n : ℕ} (input : Input n) : Bool × Trace :=
  let row := List.ofFn input.values.read
  let checked := andThenWithTrace (allWithTrace positiveWithTrace row) (fun _ => remainingWithTrace input row)
  (checked.1,wrapList n 32 (n+4) [checked.2])

def checkRowsWithTrace {n : ℕ} (input : Input n) (rows : List SignedWord) : Bool × Trace :=
  let checked := andThenWithTrace (allWithTrace positiveWithTrace rows) (fun _ => remainingWithTrace input rows)
  (checked.1,wrapList n 32 (n+4) [checked.2])

theorem checkRowsWithTrace_eq {n : ℕ} (input : Input n) (rows : List SignedWord)
    (hRows : rows = List.ofFn input.values.read) :
    checkRowsWithTrace input rows = checkWithTrace input := by
  subst rows
  rfl

theorem checkWithTrace_state {n : ℕ} (input : Input n) (hC : input.Canonical) :
    (checkWithTrace input).1 = checkBool input := by
  have hRow : ∀ word ∈ List.ofFn input.values.read,CanonicalWord word := by
    intro word hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact hC.2.2 j
  have h : (checkWithTrace input).1 = (BinaryPRGPromiseWork.checkWithWork input).1 := by
    unfold checkWithTrace BinaryPRGPromiseWork.checkWithWork
    dsimp only
    rw [andThenWithTrace_state,BinaryPRGPromiseWork.andThen_state,allWithTrace_state,
      BinaryPRGPromiseWork.allWithWork_state,remainingWithTrace_state input hC _ hRow]
    simp only [positiveWithTrace_state,BinaryPRGPromiseWork.positiveWithWork,
      BinaryPRGPromiseWork.compareWithWork,positive]
  exact h.trans (BinaryPRGPromiseWork.checkWithWork_state input)

theorem checkRowsWithTrace_state {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (checkRowsWithTrace input rows).1 = checkBool input := by
  rw [checkRowsWithTrace_eq input rows hRows]
  exact checkWithTrace_state input hC

def fieldsEnvelope (n W : ℕ) : ℕ :=
  opcodeEnvelope W+n*(opcodeEnvelope W+comparisonEnvelope W+128)+128

theorem fieldsWithTrace_usage {n : ℕ} (input : Input n) (hC : input.Canonical) :
    usage (fieldsWithTrace input (List.ofFn input.values.read)).2 ≤ fieldsEnvelope n (BinaryPRGPromiseWork.operandWidth input) := by
  let W := BinaryPRGPromiseWork.operandWidth input
  rcases BinaryPRGPromiseWork.input_widths input with ⟨ha,hb,hv,hOne,hTwo,hZero⟩
  have hTwice : width (apply .mul two input.a) ≤ W := by
    have h := BinaryPRGPromiseWork.twice_width input
    dsimp [W,BinaryPRGPromiseWork.operandWidth,BinaryPRGPromiseWork.heightCredit]
    omega
  have hData := BinaryQuadraticLifetime.applyWithTrace_state .mul two input.a two_canonical.1 hC.1.1
  have hOp := opcode_usage .mul two input.a W hTwo ha
  have hEach : ∀ word ∈ List.ofFn input.values.read,
      usage (scaledWithTrace (BinaryQuadraticLifetime.applyWithTrace .mul two input.a).1 input.b word).2 ≤
        opcodeEnvelope W+comparisonEnvelope W+64 := by
    intro word hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    rw [hData]
    exact scaledWithTrace_usage _ _ _ (apply_valid .mul _ _ two_canonical.1 hC.1.1) (hC.2.2 j).1
      W hTwice hb (hv j) (BinaryPRGPromiseWork.scaled_width input j)
  have hAll := allWithTrace_usage (scaledWithTrace (BinaryQuadraticLifetime.applyWithTrace .mul two input.a).1 input.b)
    (List.ofFn input.values.read) _ hEach
  simp only [List.length_ofFn] at hAll
  have hw := wrap_usage 24 2 [(BinaryQuadraticLifetime.applyWithTrace .mul two input.a).2,
    (allWithTrace (scaledWithTrace (BinaryQuadraticLifetime.applyWithTrace .mul two input.a).1 input.b) (List.ofFn input.values.read)).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (fieldsWithTrace input (List.ofFn input.values.read)).2 ≤ _ at hw
  unfold fieldsEnvelope
  change _ ≤ opcodeEnvelope W+n*(opcodeEnvelope W+comparisonEnvelope W+128)+128
  have hAssoc : opcodeEnvelope W+comparisonEnvelope W+64+64 = opcodeEnvelope W+comparisonEnvelope W+128 := by omega
  rw [hAssoc] at hAll
  omega

def remainingEnvelope (n W : ℕ) : ℕ :=
  BinaryStoredWordSumLifetime.envelope n W+fieldsEnvelope n W+5*comparisonEnvelope W+512

theorem remainingWithTrace_usage {n : ℕ} (input : Input n) (hC : input.Canonical) :
    usage (remainingWithTrace input (List.ofFn input.values.read)).2 ≤ remainingEnvelope n (BinaryPRGPromiseWork.operandWidth input) := by
  let row := List.ofFn input.values.read
  let W := BinaryPRGPromiseWork.operandWidth input
  let C := comparisonEnvelope W
  have hRow : ∀ word ∈ row,CanonicalWord word := by
    intro word hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact hC.2.2 j
  rcases BinaryPRGPromiseWork.input_widths input with ⟨ha,hb,hv,hOne,hTwo,hZero⟩
  have hCredit : 1+2*BinaryStoredWordSumWork.credit row ≤ W := by
    have h := BinaryPRGPromiseWork.row_credit input
    change BinaryStoredWordSumWork.credit row ≤ BinaryPRGPromiseWork.heightCredit input at h
    dsimp [W,BinaryPRGPromiseWork.operandWidth]
    omega
  have hSum := BinaryStoredWordSumLifetime.sumWithTrace_usage row hRow W hCredit
  have hWidth : width (BinaryStoredWordSumLifetime.sumWithTrace row).1 ≤ W := by
    rw [BinaryStoredWordSumLifetime.sumWithTrace_state row hRow]
    exact BinaryPRGPromiseWork.sum_width input hC
  have hEq := equalWithTrace_usage (BinaryStoredWordSumLifetime.sumWithTrace row).1 one W hWidth hOne
  have hA := positiveWithTrace_usage input.a W ha hZero
  have hB := positiveWithTrace_usage input.b W hb hZero
  have hOrder := comparison_usage input.b input.a W hb ha
  have hFields := fieldsWithTrace_usage input hC
  have hChecks := andThenWithTrace_usage (BinaryQuadraticExpressionLifetime.compareWithTrace input.b input.a)
    (fun _ => fieldsWithTrace input row) _ _ hOrder hFields
  have hBudgetB := andThenWithTrace_usage (positiveWithTrace input.b)
    (fun _ => andThenWithTrace (BinaryQuadraticExpressionLifetime.compareWithTrace input.b input.a)
      (fun _ => fieldsWithTrace input row)) _ _ hB hChecks
  have hBudgetA := andThenWithTrace_usage (positiveWithTrace input.a)
    (fun _ => andThenWithTrace (positiveWithTrace input.b) (fun _ =>
      andThenWithTrace (BinaryQuadraticExpressionLifetime.compareWithTrace input.b input.a)
        (fun _ => fieldsWithTrace input row))) _ _ hA hBudgetB
  have hEqual := andThenWithTrace_usage (equalWithTrace (BinaryStoredWordSumLifetime.sumWithTrace row).1 one)
    (fun _ => andThenWithTrace (positiveWithTrace input.a) (fun _ =>
      andThenWithTrace (positiveWithTrace input.b) (fun _ =>
        andThenWithTrace (BinaryQuadraticExpressionLifetime.compareWithTrace input.b input.a)
          (fun _ => fieldsWithTrace input row)))) _ _ hEq hBudgetA
  let later := andThenWithTrace (equalWithTrace (BinaryStoredWordSumLifetime.sumWithTrace row).1 one)
    (fun _ => andThenWithTrace (positiveWithTrace input.a) (fun _ =>
      andThenWithTrace (positiveWithTrace input.b) (fun _ =>
        andThenWithTrace (BinaryQuadraticExpressionLifetime.compareWithTrace input.b input.a)
          (fun _ => fieldsWithTrace input row))))
  have hw := wrap_usage 24 2 [(BinaryStoredWordSumLifetime.sumWithTrace row).2,later.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (remainingWithTrace input row).2 ≤ _ at hw
  change usage later.2 ≤ _ at hEqual
  simp only [row,List.length_ofFn] at hSum
  unfold remainingEnvelope
  change _ ≤ BinaryStoredWordSumLifetime.envelope n W+fieldsEnvelope n W+5*comparisonEnvelope W+512
  dsimp only [row,W] at *
  omega

def envelope (n S : ℕ) : ℕ :=
  let W := 12*(S+n+3)+10
  n*(comparisonEnvelope W+128)+remainingEnvelope n W+2*n+256

theorem envelope_mono {n m S T : ℕ} (hn : n ≤ m) (hS : S ≤ T) :
    envelope n S ≤ envelope m T := by
  unfold envelope remainingEnvelope fieldsEnvelope comparisonEnvelope
    BinaryStoredWordSumLifetime.envelope BinaryLifetimeUsage.opcodeEnvelope
    BinaryQuadraticLifetime.opcodeBound BinaryQuadraticLifetime.opcodeFrames
  dsimp only
  gcongr

theorem checkWithTrace_usage {n : ℕ} (input : Input n) (hC : input.Canonical) :
    usage (checkWithTrace input).2 ≤ envelope n (BinaryPRGPreparationWork.storedInputWidth input) := by
  let row := List.ofFn input.values.read
  let W := BinaryPRGPromiseWork.operandWidth input
  rcases BinaryPRGPromiseWork.input_widths input with ⟨ha,hb,hv,hOne,hTwo,hZero⟩
  have hAll := allWithTrace_usage positiveWithTrace row (comparisonEnvelope W+64) (by
    intro word hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact positiveWithTrace_usage _ W (hv j) hZero)
  have hRemaining := remainingWithTrace_usage input hC
  have hChecked := andThenWithTrace_usage (allWithTrace positiveWithTrace row)
    (fun _ => remainingWithTrace input row) _ _ hAll hRemaining
  let checked := andThenWithTrace (allWithTrace positiveWithTrace row) (fun _ => remainingWithTrace input row)
  have hw := wrapList_usage n 32 (n+4) [checked.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (checkWithTrace input).2 ≤ _ at hw
  change usage checked.2 ≤ _ at hChecked
  simp only [row,List.length_ofFn] at hChecked
  unfold envelope
  change _ ≤ n*(comparisonEnvelope W+128)+remainingEnvelope n W+2*n+256
  have hAssoc : comparisonEnvelope W+64+64 = comparisonEnvelope W+128 := by omega
  rw [hAssoc] at hChecked
  simp only [row,List.length_ofFn] at hAll
  dsimp only [row,W] at *
  omega

theorem checkRowsWithTrace_usage {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    usage (checkRowsWithTrace input rows).2 ≤ envelope n (BinaryPRGPreparationWork.storedInputWidth input) := by
  rw [checkRowsWithTrace_eq input rows hRows]
  exact checkWithTrace_usage input hC

theorem all_prefix {n : ℕ} (input : Input n) (hC : input.Canonical) (borrowed steps : ℕ) :
    retainedHeap borrowed (checkWithTrace input).2 steps ≤ borrowed+envelope n (BinaryPRGPreparationWork.storedInputWidth input) ∧
    framePeak ((checkWithTrace input).2.take steps) ≤ envelope n (BinaryPRGPreparationWork.storedInputWidth input) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (checkWithTrace_usage input hC) borrowed steps

end Blotto.BinaryPRGPromiseLifetime
