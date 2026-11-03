import Blotto.BinaryStoredWordSumMeasured
import Blotto.BinaryPRGPromiseLifetime
import Blotto.BinaryPRGGameFrameMeasured
import Blotto.BinaryPRGCheckedGameLifetime

/-! One ordered promise check consumes the retained canonical row. Actual
measured quadratic sums/opcodes/comparisons and delayed Boolean guards return
old results/traces with work. Stored-input width bounds every reached operand
without assuming promise acceptance. Native reference/observer/GC joins remain. -/
namespace Blotto.BinaryPRGPromiseMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryPRGRecognition
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryPRGPromiseControlMeasured
set_option autoImplicit false
set_option maxHeartbeats 3000000

def fields {n : ℕ} (input : Input n) (row : List SignedWord) : (Bool × Trace) × ℕ :=
  let twice := BinaryQuadraticMeasured.apply .mul two input.a
  let tested := BinaryPRGPromiseControlMeasured.all (scaled twice.1.1 input.b) row
  ((tested.1.1,wrap 24 2 [twice.1.2,tested.1.2]),twice.2+tested.2+8)

theorem fields_erases {n : ℕ} (input : Input n) (row : List SignedWord) :
    (fields input row).1 = BinaryPRGPromiseLifetime.fieldsWithTrace input row := by
  simp only [fields,BinaryPRGPromiseLifetime.fieldsWithTrace,all_erases,scaled_erases,
    BinaryQuadraticMeasured.apply_erases]

def remaining {n : ℕ} (input : Input n) (row : List SignedWord) : (Bool × Trace) × ℕ :=
  let summed := BinaryStoredWordSumMeasured.sum row
  let later := andThen (BinaryPRGPromiseControlMeasured.equal summed.1.1 one) (fun _ =>
    andThen (BinaryPRGPromiseControlMeasured.positive input.a) (fun _ =>
      andThen (BinaryPRGPromiseControlMeasured.positive input.b) (fun _ =>
        andThen (BinaryQuadraticExpressionMeasured.compare input.b input.a) (fun _ => fields input row))))
  ((later.1.1,wrap 24 2 [summed.1.2,later.1.2]),summed.2+later.2+8)

theorem remaining_erases {n : ℕ} (input : Input n) (row : List SignedWord) :
    (remaining input row).1 = BinaryPRGPromiseLifetime.remainingWithTrace input row := by
  simp only [remaining,BinaryPRGPromiseLifetime.remainingWithTrace,BinaryStoredWordSumMeasured.sum_erases,
    andThen_erases,equal_erases,positive_erases,BinaryQuadraticExpressionMeasured.compare_erases,fields_erases]

def checkRows {n : ℕ} (input : Input n) (rows : List SignedWord) : (Bool × Trace) × ℕ :=
  let checked := andThen (BinaryPRGPromiseControlMeasured.all BinaryPRGPromiseControlMeasured.positive rows)
    (fun _ => remaining input rows)
  ((checked.1.1,wrapList n 32 (n+4) [checked.1.2]),checked.2+4)

theorem checkRows_erases {n : ℕ} (input : Input n) (rows : List SignedWord) :
    (checkRows input rows).1 = BinaryPRGPromiseLifetime.checkRowsWithTrace input rows := by
  simp only [checkRows,BinaryPRGPromiseLifetime.checkRowsWithTrace,andThen_erases,
    all_erases,positive_erases,remaining_erases]

theorem checkRows_state {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (checkRows input rows).1.1 = checkBool input := by
  rw [checkRows_erases]
  exact BinaryPRGPromiseLifetime.checkRowsWithTrace_state input hC rows hRows

def fieldsPrice (n W : ℕ) : ℕ := opcodePrice W+n*(opcodePrice W+comparisonPrice W+12)+12
def remainingPrice (n W : ℕ) : ℕ := BinaryStoredWordSumMeasured.price n W+fieldsPrice n W+5*comparisonPrice W+64
def price (n W : ℕ) : ℕ := n*(comparisonPrice W+8)+remainingPrice n W+16

theorem canonical_row {n : ℕ} (input : Input n) (hC : input.Canonical) :
    ∀ word ∈ List.ofFn input.values.read,CanonicalWord word := by
  intro word hw
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
  exact hC.2.2 j

theorem fields_work {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (fields input rows).2 ≤ fieldsPrice n (BinaryPRGPromiseWork.operandWidth input) := by
  subst rows
  let W := BinaryPRGPromiseWork.operandWidth input
  rcases BinaryPRGPromiseWork.input_widths input with ⟨ha,hb,hv,hOne,hTwo,hZero⟩
  have hTwice : width (apply .mul two input.a) ≤ W := by
    have h := BinaryPRGPromiseWork.twice_width input
    dsimp [W,BinaryPRGPromiseWork.operandWidth,BinaryPRGPromiseWork.heightCredit]
    omega
  have hData : (BinaryQuadraticMeasured.apply .mul two input.a).1.1 = apply .mul two input.a := by
    rw [BinaryQuadraticMeasured.apply_erases,
      BinaryQuadraticLifetime.applyWithTrace_state .mul two input.a two_canonical.1 hC.1.1]
  have hOp := opcode_bound .mul two input.a W hTwo ha
  have hEach : ∀ word ∈ List.ofFn input.values.read,
      (scaled (BinaryQuadraticMeasured.apply .mul two input.a).1.1 input.b word).2 ≤
        opcodePrice W+comparisonPrice W+8 := by
    intro word hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    rw [hData]
    exact scaled_work _ _ _ (apply_valid .mul _ _ two_canonical.1 hC.1.1) (hC.2.2 j).1
      W hTwice hb (hv j) (BinaryPRGPromiseWork.scaled_width input j)
  have hAll := all_work (scaled (BinaryQuadraticMeasured.apply .mul two input.a).1.1 input.b)
    (List.ofFn input.values.read) _ hEach
  simp only [List.length_ofFn] at hAll
  rw [show opcodePrice W+comparisonPrice W+8+4 = opcodePrice W+comparisonPrice W+12 by omega] at hAll
  change (BinaryQuadraticMeasured.apply .mul two input.a).2+
    (BinaryPRGPromiseControlMeasured.all
      (scaled (BinaryQuadraticMeasured.apply .mul two input.a).1.1 input.b) (List.ofFn input.values.read)).2+8 ≤ _
  change _ ≤ opcodePrice W+n*(opcodePrice W+comparisonPrice W+12)+12
  omega

theorem remaining_work {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (remaining input rows).2 ≤ remainingPrice n (BinaryPRGPromiseWork.operandWidth input) := by
  subst rows
  let row := List.ofFn input.values.read
  let W := BinaryPRGPromiseWork.operandWidth input
  let C := comparisonPrice W
  rcases BinaryPRGPromiseWork.input_widths input with ⟨ha,hb,hv,hOne,hTwo,hZero⟩
  have hCredit : 1+2*BinaryStoredWordSumWork.credit row ≤ W := by
    have h := BinaryPRGPromiseWork.row_credit input
    dsimp only [row,W,BinaryPRGPromiseWork.operandWidth]
    omega
  have hSum := BinaryStoredWordSumMeasured.sum_work row (canonical_row input hC) W hCredit
  have hSumWidth : width (BinaryStoredWordSumMeasured.sum row).1.1 ≤ W := by
    rw [BinaryStoredWordSumMeasured.sum_data row (canonical_row input hC)]
    exact BinaryPRGPromiseWork.sum_width input hC
  have hFields := fields_work input hC row rfl
  change (fields input row).2 ≤ fieldsPrice n W at hFields
  have hCmp := comparison_bound input.b input.a W hb ha
  have hA := positive_work input.a W ha hZero
  have hB := positive_work input.b W hb hZero
  have hEq := equal_work (BinaryStoredWordSumMeasured.sum row).1.1 one W hSumWidth hOne
  have h3 := andThen_work (BinaryQuadraticExpressionMeasured.compare input.b input.a)
    (fun _ => fields input row) _ _ hCmp hFields
  have h2 := andThen_work (BinaryPRGPromiseControlMeasured.positive input.b)
    (fun _ => andThen (BinaryQuadraticExpressionMeasured.compare input.b input.a) (fun _ => fields input row)) _ _ hB h3
  have h1 := andThen_work (BinaryPRGPromiseControlMeasured.positive input.a)
    (fun _ => andThen (BinaryPRGPromiseControlMeasured.positive input.b)
      (fun _ => andThen (BinaryQuadraticExpressionMeasured.compare input.b input.a) (fun _ => fields input row))) _ _ hA h2
  have h0 := andThen_work (BinaryPRGPromiseControlMeasured.equal (BinaryStoredWordSumMeasured.sum row).1.1 one)
    (fun _ => andThen (BinaryPRGPromiseControlMeasured.positive input.a)
      (fun _ => andThen (BinaryPRGPromiseControlMeasured.positive input.b)
        (fun _ => andThen (BinaryQuadraticExpressionMeasured.compare input.b input.a) (fun _ => fields input row)))) _ _ hEq h1
  simp only [List.length_ofFn,row] at hSum
  change (BinaryStoredWordSumMeasured.sum row).2 ≤ BinaryStoredWordSumMeasured.price n W at hSum
  change (BinaryStoredWordSumMeasured.sum row).2+_+8 ≤ _
  change _ ≤ BinaryStoredWordSumMeasured.price n W+fieldsPrice n W+5*comparisonPrice W+64
  dsimp only [row] at h0 hSum ⊢
  omega

theorem checkRows_work {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (checkRows input rows).2 ≤ price n (BinaryPRGPromiseWork.operandWidth input) := by
  have hLength : rows.length = n := by rw [hRows,List.length_ofFn]
  let W := BinaryPRGPromiseWork.operandWidth input
  rcases BinaryPRGPromiseWork.input_widths input with ⟨ha,hb,hv,hOne,hTwo,hZero⟩
  have hAll := all_work BinaryPRGPromiseControlMeasured.positive rows (comparisonPrice W+4) (by
    intro word hw
    rw [hRows] at hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact positive_work _ W (hv j) hZero)
  have hRemaining := remaining_work input hC rows hRows
  change (remaining input rows).2 ≤ remainingPrice n W at hRemaining
  have hChecked := andThen_work (BinaryPRGPromiseControlMeasured.all BinaryPRGPromiseControlMeasured.positive rows)
    (fun _ => remaining input rows) _ _ hAll hRemaining
  rw [hLength] at hChecked
  rw [show comparisonPrice W+4+4 = comparisonPrice W+8 by omega] at hChecked
  change (andThen (BinaryPRGPromiseControlMeasured.all BinaryPRGPromiseControlMeasured.positive rows)
    (fun _ => remaining input rows)).2+4 ≤ _
  unfold price
  change _ ≤ n*(comparisonPrice W+8)+remainingPrice n W+16
  omega

theorem price_mono {n m W V : ℕ} (hn : n ≤ m) (hW : W ≤ V) : price n W ≤ price m V := by
  unfold price remainingPrice fieldsPrice BinaryStoredWordSumMeasured.price opcodePrice comparisonPrice
    BinaryQuadraticExpression.uniformPrice
  gcongr

theorem raw_work {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read)
    (L : ℕ) (hn : n ≤ L) (hWidth : BinaryPRGPreparationWork.storedInputWidth input ≤ L+2) :
    (checkRows input rows).2 ≤ 2000000000*(L+1)^3 := by
  have hW : BinaryPRGPromiseWork.operandWidth input ≤ 24*L+70 := by
    unfold BinaryPRGPromiseWork.operandWidth BinaryPRGPromiseWork.heightCredit
    omega
  have h := (checkRows_work input hC rows hRows).trans (price_mono hn hW)
  have hPoly : price L (24*L+70) ≤ 2000000000*(L+1)^3 := by
    unfold price remainingPrice fieldsPrice BinaryStoredWordSumMeasured.price opcodePrice comparisonPrice
      BinaryQuadraticExpression.uniformPrice
    ring_nf
    omega
  exact h.trans hPoly

theorem parsed_work (frame : List Bool) (parsed : (Σ n,BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (hParsed : (BinaryPRGGameFrameMeasured.read frame).1.1 = some parsed) :
    (checkRows parsed.1.2.game.input parsed.1.2.rows).2 ≤ 2000000000*(frame.length+1)^3 := by
  have hOld : (BinaryPRGGameFrameLifetime.readWithTrace frame).1 = some parsed :=
    (congrArg Prod.fst (BinaryPRGGameFrameMeasured.read_erases frame)).symm.trans hParsed
  have hSizes := BinaryPRGCheckedGameLifetime.parsed_sizes frame parsed hOld
  exact raw_work parsed.1.2.game.input parsed.1.2.game.canonical parsed.1.2.rows
    parsed.1.2.rows_readback frame.length hSizes.1 hSizes.2

theorem parsed_game_joint (frame : List Bool) (parsed : (Σ n,BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (hParsed : (BinaryPRGGameFrameMeasured.read frame).1.1 = some parsed) :
    (BinaryPRGGameFrameMeasured.read frame).2+(checkRows parsed.1.2.game.input parsed.1.2.rows).2 ≤
      2000010000*(frame.length+1)^3 := by
  have hGame := (BinaryPRGGameFrameMeasured.read_work frame).trans
    (BinaryPRGGameFrameMeasured.price_polynomial frame.length)
  have hCheck := parsed_work frame parsed hParsed
  nlinarith only [hGame,hCheck]

theorem checkRows_usage {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    usage (checkRows input rows).1.2 ≤ BinaryPRGPromiseLifetime.envelope n (BinaryPRGPreparationWork.storedInputWidth input) := by
  rw [checkRows_erases]
  exact BinaryPRGPromiseLifetime.checkRowsWithTrace_usage input hC rows hRows

theorem all_prefix {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) (borrowed steps : ℕ) :
    retainedHeap borrowed (checkRows input rows).1.2 steps ≤
      borrowed+BinaryPRGPromiseLifetime.envelope n (BinaryPRGPreparationWork.storedInputWidth input) ∧
    framePeak ((checkRows input rows).1.2.take steps) ≤
      BinaryPRGPromiseLifetime.envelope n (BinaryPRGPreparationWork.storedInputWidth input) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (checkRows_usage input hC rows hRows) _ steps

end Blotto.BinaryPRGPromiseMeasured
