import Blotto.BinarySeedPreparationSpace
import Blotto.BinaryRationalOpcodeAllocation

/-! Ghost source allocation trace for the original scaling/framing suffix of
an actual prepared-block draw. Primitive opcode reservations reuse the retained
allocation contracts for their actual Boolean arithmetic. Both scaling array
builds are charged, permitting full-capacity prefix copies without uniqueness.
Stored coordinate framing traces its actual replicate/append/cons operations;
the retained header and the scaled word tails remain shared inputs.

This suffix contract does not price the preceding resource/terminal/factory/
fallback computation. It accepts the actual returned normalized row, and exact
source bounds derive its width on every bit path, including global fallback.
The retained-reservation policy releases no preceding opcode reservation; it
provides a conservative source space envelope, not reclaimed R230 space or a
native allocator/stack/GC certificate. Opcode-storage reservation cells include that primitive
model's internal control footprint; frame snapshots below bound the suffix
controller activations. A scalar/record backend must still realize the exact
remaining work counters, OfFn indices, array capacities and activation records
identified at the end of this module; physical layout remains separate. -/
namespace Blotto.BinaryPRGOutputLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGOutputPrimitiveWork RationalLottoResourceSystem
open scoped BigOperators

def replicateWithTrace : ℕ → Bool → List Bool × Trace
  | 0, _ => ([],[.frames 1])
  | n+1, bit =>
      let earlier := replicateWithTrace n bit
      (bit :: earlier.1,[.frames 1,.listAllocation 1] ++ under 1 earlier.2)

theorem replicateWithTrace_state (n : ℕ) (bit : Bool) : (replicateWithTrace n bit).1 = List.replicate n bit := by
  induction n with
  | zero => rfl
  | succ n ih => simp [replicateWithTrace,ih,List.replicate_succ]

theorem replicateWithTrace_cells (n : ℕ) (bit : Bool) : listCells (replicateWithTrace n bit).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [replicateWithTrace,listCells,ih,Nat.add_comm]

theorem replicateWithTrace_frames (n : ℕ) (bit : Bool) : framePeak (replicateWithTrace n bit).2 ≤ n+1 := by
  induction n with
  | zero => simp [replicateWithTrace,framePeak]
  | succ n ih =>
      have hu := framePeak_under 1 (replicateWithTrace n bit).2
      simp only [replicateWithTrace,framePeak_append,framePeak]
      omega

def appendWithTrace : List Bool → List Bool → List Bool × Trace
  | [], right => (right,[.frames 1])
  | bit :: left, right =>
      let earlier := appendWithTrace left right
      (bit :: earlier.1,[.frames 1,.listAllocation 1] ++ under 1 earlier.2)

theorem appendWithTrace_state (left right : List Bool) : (appendWithTrace left right).1 = left ++ right := by
  induction left with
  | nil => rfl
  | cons bit left ih => simp [appendWithTrace,ih]

theorem appendWithTrace_cells (left right : List Bool) : listCells (appendWithTrace left right).2 = left.length := by
  induction left with
  | nil => rfl
  | cons bit left ih => simp [appendWithTrace,listCells,ih,Nat.add_comm]

theorem appendWithTrace_frames (left right : List Bool) : framePeak (appendWithTrace left right).2 ≤ left.length+1 := by
  induction left with
  | nil => simp [appendWithTrace,framePeak]
  | cons bit left ih =>
      have hu := framePeak_under 1 (appendWithTrace left right).2
      simp only [appendWithTrace,framePeak_append,framePeak,List.length_cons]
      omega

def payloadWithTrace (bits : List Bool) : List Bool × Trace :=
  let ruler := replicateWithTrace bits.length false
  let delimiter := true :: bits
  let result := appendWithTrace ruler.1 delimiter
  (result.1,[.frames 2] ++ under 2 ruler.2 ++ [.listAllocation 1] ++ under 2 result.2)

theorem payloadWithTrace_state (bits : List Bool) : (payloadWithTrace bits).1 = BinaryStoredRowFrame.payload bits := by
  simp [payloadWithTrace,appendWithTrace_state,replicateWithTrace_state,BinaryStoredRowFrame.payload]

theorem payloadWithTrace_cells (bits : List Bool) : listCells (payloadWithTrace bits).2 = 2*bits.length+1 := by
  simp [payloadWithTrace,listCells,replicateWithTrace_cells,appendWithTrace_cells,replicateWithTrace_state]
  omega

theorem payloadWithTrace_frames (bits : List Bool) : framePeak (payloadWithTrace bits).2 ≤ bits.length+3 := by
  have hr := replicateWithTrace_frames bits.length false
  have ha := appendWithTrace_frames (replicateWithTrace bits.length false).1 (true::bits)
  have hRulerLength : (replicateWithTrace bits.length false).1.length = bits.length := by simp [replicateWithTrace_state]
  rw [hRulerLength] at ha
  have hru := framePeak_under 2 (replicateWithTrace bits.length false).2
  have hau := framePeak_under 2 (appendWithTrace (replicateWithTrace bits.length false).1 (true::bits)).2
  simp only [payloadWithTrace,framePeak_append,framePeak]
  omega

def wordWithTrace (input : SignedWord) : List Bool × Trace :=
  let numerator := payloadWithTrace input.numerator
  let denominator := payloadWithTrace input.denominator
  let joined := appendWithTrace numerator.1 denominator.1
  (input.negative :: joined.1,[.frames 2] ++ under 2 numerator.2 ++ under 2 denominator.2 ++
    under 2 joined.2 ++ [.listAllocation 1])

theorem wordWithTrace_state (input : SignedWord) : (wordWithTrace input).1 = BinaryStoredRowFrame.word input := by
  simp [wordWithTrace,payloadWithTrace_state,appendWithTrace_state,BinaryStoredRowFrame.word]

theorem payload_length (bits : List Bool) : (BinaryStoredRowFrame.payload bits).length = 2*bits.length+1 := by
  simp [BinaryStoredRowFrame.payload]
  omega

theorem word_length (input : SignedWord) : (BinaryStoredRowFrame.word input).length =
    2*input.numerator.length+2*input.denominator.length+3 := by
  simp [BinaryStoredRowFrame.word,payload_length]
  omega

theorem wordWithTrace_cells (input : SignedWord) : listCells (wordWithTrace input).2 ≤
    2*(BinaryStoredRowFrame.word input).length := by
  simp [wordWithTrace,listCells,payloadWithTrace_cells,appendWithTrace_cells,payloadWithTrace_state,payload_length,word_length]
  omega

theorem wordWithTrace_frames (input : SignedWord) : framePeak (wordWithTrace input).2 ≤
    (BinaryStoredRowFrame.word input).length+5 := by
  have hn := payloadWithTrace_frames input.numerator
  have hd := payloadWithTrace_frames input.denominator
  have ha := appendWithTrace_frames (payloadWithTrace input.numerator).1 (payloadWithTrace input.denominator).1
  have hNumeratorLength : (payloadWithTrace input.numerator).1.length = 2*input.numerator.length+1 := by
    rw [payloadWithTrace_state,payload_length]
  rw [hNumeratorLength] at ha
  have hnu := framePeak_under 2 (payloadWithTrace input.numerator).2
  have hdu := framePeak_under 2 (payloadWithTrace input.denominator).2
  have hau := framePeak_under 2 (appendWithTrace (payloadWithTrace input.numerator).1 (payloadWithTrace input.denominator).1).2
  simp only [wordWithTrace,framePeak_append,framePeak,word_length]
  omega

def wordsWithTrace : List SignedWord → List Bool × Trace
  | [] => ([],[.frames 1])
  | input :: rest =>
      let word := wordWithTrace input
      let later := wordsWithTrace rest
      let combined := appendWithTrace word.1 later.1
      (combined.1,[.frames 2] ++ under 2 word.2 ++ under 2 later.2 ++ under 2 combined.2)

theorem wordsWithTrace_state (inputs : List SignedWord) : (wordsWithTrace inputs).1 = BinaryStoredRowFrame.words inputs := by
  induction inputs with
  | nil => rfl
  | cons input rest ih => simp [wordsWithTrace,appendWithTrace_state,wordWithTrace_state,ih,BinaryStoredRowFrame.words]

theorem wordsWithTrace_cells (inputs : List SignedWord) : listCells (wordsWithTrace inputs).2 ≤
    3*(BinaryStoredRowFrame.words inputs).length := by
  induction inputs with
  | nil => simp [wordsWithTrace,listCells,BinaryStoredRowFrame.words]
  | cons input rest ih =>
      have hw := wordWithTrace_cells input
      simp only [wordsWithTrace,listCells_append,listCells,listCells_under,appendWithTrace_cells,
        wordWithTrace_state,BinaryStoredRowFrame.words,List.length_append]
      omega

theorem wordsWithTrace_frames (inputs : List SignedWord) : framePeak (wordsWithTrace inputs).2 ≤
    2*inputs.length + (BinaryStoredRowFrame.words inputs).length + 5 := by
  induction inputs with
  | nil => simp [wordsWithTrace,framePeak,BinaryStoredRowFrame.words]
  | cons input rest ih =>
      have hw := wordWithTrace_frames input
      have ha := appendWithTrace_frames (wordWithTrace input).1 (wordsWithTrace rest).1
      have hWordLength := congrArg List.length (wordWithTrace_state input)
      rw [hWordLength] at ha
      have hwu := framePeak_under 2 (wordWithTrace input).2
      have hlu := framePeak_under 2 (wordsWithTrace rest).2
      have hau := framePeak_under 2 (appendWithTrace (wordWithTrace input).1 (wordsWithTrace rest).1).2
      simp only [wordsWithTrace,framePeak_append,framePeak,BinaryStoredRowFrame.words,List.length_append,List.length_cons]
      omega

@[simp] theorem replicateWithTrace_arrays (n : ℕ) (bit : Bool) : arraySlots (replicateWithTrace n bit).2 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [replicateWithTrace,arraySlots,ih]

@[simp] theorem appendWithTrace_arrays (left right : List Bool) : arraySlots (appendWithTrace left right).2 = 0 := by
  induction left with
  | nil => rfl
  | cons bit left ih => simp [appendWithTrace,arraySlots,ih]

@[simp] theorem payloadWithTrace_arrays (bits : List Bool) : arraySlots (payloadWithTrace bits).2 = 0 := by
  simp [payloadWithTrace,arraySlots]

@[simp] theorem wordWithTrace_arrays (input : SignedWord) : arraySlots (wordWithTrace input).2 = 0 := by
  simp [wordWithTrace,arraySlots]

@[simp] theorem wordsWithTrace_arrays (inputs : List SignedWord) : arraySlots (wordsWithTrace inputs).2 = 0 := by
  induction inputs with
  | nil => rfl
  | cons input rest ih => simp [wordsWithTrace,arraySlots,ih]

def frameWithTrace (header : List Bool) (inputs : List SignedWord) : List Bool × Trace :=
  let words := wordsWithTrace inputs
  let joined := appendWithTrace header words.1
  (joined.1,[.frames 2] ++ under 2 words.2 ++ under 2 joined.2)

theorem frameWithTrace_state (header : List Bool) (inputs : List SignedWord) :
    (frameWithTrace header inputs).1 = header ++ BinaryStoredRowFrame.words inputs := by
  simp [frameWithTrace,appendWithTrace_state,wordsWithTrace_state]

theorem frameWithTrace_cells (header : List Bool) (inputs : List SignedWord) :
    listCells (frameWithTrace header inputs).2 ≤ header.length+3*(BinaryStoredRowFrame.words inputs).length := by
  have h := wordsWithTrace_cells inputs
  simp only [frameWithTrace,listCells_append,listCells,listCells_under,appendWithTrace_cells]
  omega

theorem frameWithTrace_frames (header : List Bool) (inputs : List SignedWord) :
    framePeak (frameWithTrace header inputs).2 ≤ header.length+2*inputs.length+(BinaryStoredRowFrame.words inputs).length+7 := by
  have h := wordsWithTrace_frames inputs
  have ha := appendWithTrace_frames header (wordsWithTrace inputs).1
  have hwu := framePeak_under 2 (wordsWithTrace inputs).2
  have hau := framePeak_under 2 (appendWithTrace header (wordsWithTrace inputs).1).2
  simp only [frameWithTrace,framePeak_append,framePeak]
  omega

@[simp] theorem frameWithTrace_arrays (header : List Bool) (inputs : List SignedWord) :
    arraySlots (frameWithTrace header inputs).2 = 0 := by simp [frameWithTrace,arraySlots]

-- These observers really rebuild payload/word lists in the original source;
-- a length observer is not assumed allocation-free or common-subexpression
-- eliminated. The returned numeric ledger is exactly the retained observer.
def payloadVisitsWithTrace (bits : List Bool) : ℕ × Trace :=
  let payload := payloadWithTrace bits
  (2*bits.length+payload.1.length+1,under 2 payload.2 ++ [.frames (payload.1.length+3)])

theorem payloadVisitsWithTrace_state (bits : List Bool) :
    (payloadVisitsWithTrace bits).1 = BinaryStoredRowFrameWork.payloadVisits bits := by
  simp [payloadVisitsWithTrace,payloadWithTrace_state,BinaryStoredRowFrameWork.payloadVisits]

def wordVisitsWithTrace (input : SignedWord) : ℕ × Trace :=
  let numerator := payloadVisitsWithTrace input.numerator
  let denominator := payloadVisitsWithTrace input.denominator
  let extra := payloadWithTrace input.numerator
  (numerator.1+denominator.1+extra.1.length+1,
    under 2 numerator.2 ++ under 2 denominator.2 ++ under 2 extra.2 ++ [.frames (extra.1.length+3)])

theorem wordVisitsWithTrace_state (input : SignedWord) :
    (wordVisitsWithTrace input).1 = BinaryStoredRowFrameWork.wordVisits input := by
  simp [wordVisitsWithTrace,payloadVisitsWithTrace_state,payloadWithTrace_state,BinaryStoredRowFrameWork.wordVisits]

theorem wordVisitsWithTrace_cells (input : SignedWord) : listCells (wordVisitsWithTrace input).2 ≤
    2*(BinaryStoredRowFrame.word input).length := by
  simp [wordVisitsWithTrace,payloadVisitsWithTrace,listCells,payloadWithTrace_cells,word_length]
  omega

def wordsVisitsWithTrace : List SignedWord → ℕ × Trace
  | [] => (0,[.frames 1])
  | input :: rest =>
      let localVisits := wordVisitsWithTrace input
      let encoded := wordWithTrace input
      let later := wordsVisitsWithTrace rest
      (localVisits.1+encoded.1.length+later.1+1,
        under 2 localVisits.2 ++ under 2 encoded.2 ++ [.frames (encoded.1.length+3)] ++ under 2 later.2)

theorem wordsVisitsWithTrace_state (inputs : List SignedWord) :
    (wordsVisitsWithTrace inputs).1 = BinaryStoredRowFrameWork.wordsVisits inputs := by
  induction inputs with
  | nil => rfl
  | cons input rest ih => simp [wordsVisitsWithTrace,wordVisitsWithTrace_state,wordWithTrace_state,ih,BinaryStoredRowFrameWork.wordsVisits]

theorem wordsVisitsWithTrace_cells (inputs : List SignedWord) :
    listCells (wordsVisitsWithTrace inputs).2 ≤ 4*(BinaryStoredRowFrame.words inputs).length := by
  induction inputs with
  | nil => simp [wordsVisitsWithTrace,listCells,BinaryStoredRowFrame.words]
  | cons input rest ih =>
      have hl := wordVisitsWithTrace_cells input
      have hw := wordWithTrace_cells input
      simp only [wordsVisitsWithTrace,listCells_append,listCells_under,listCells,BinaryStoredRowFrame.words,List.length_append]
      omega

@[simp] theorem payloadVisitsWithTrace_arrays (bits : List Bool) : arraySlots (payloadVisitsWithTrace bits).2 = 0 := by
  simp [payloadVisitsWithTrace,arraySlots]

@[simp] theorem wordVisitsWithTrace_arrays (input : SignedWord) : arraySlots (wordVisitsWithTrace input).2 = 0 := by
  simp [wordVisitsWithTrace,arraySlots]

@[simp] theorem wordsVisitsWithTrace_arrays (inputs : List SignedWord) : arraySlots (wordsVisitsWithTrace inputs).2 = 0 := by
  induction inputs with
  | nil => rfl
  | cons input rest ih => simp [wordsVisitsWithTrace,arraySlots,ih]

theorem payloadVisitsWithTrace_frames (bits : List Bool) :
    framePeak (payloadVisitsWithTrace bits).2 ≤ (BinaryStoredRowFrame.payload bits).length+5 := by
  have hp := payloadWithTrace_frames bits
  have hu := framePeak_under 2 (payloadWithTrace bits).2
  simp only [payloadVisitsWithTrace,framePeak_append,framePeak,payloadWithTrace_state,payload_length]
  omega

theorem wordVisitsWithTrace_frames (input : SignedWord) :
    framePeak (wordVisitsWithTrace input).2 ≤ (BinaryStoredRowFrame.word input).length+7 := by
  have hn := payloadVisitsWithTrace_frames input.numerator
  have hd := payloadVisitsWithTrace_frames input.denominator
  have he := payloadWithTrace_frames input.numerator
  have hnu := framePeak_under 2 (payloadVisitsWithTrace input.numerator).2
  have hdu := framePeak_under 2 (payloadVisitsWithTrace input.denominator).2
  have heu := framePeak_under 2 (payloadWithTrace input.numerator).2
  simp only [wordVisitsWithTrace,framePeak_append,framePeak,payloadWithTrace_state,payload_length,word_length] at hn hd ⊢
  omega

theorem wordsVisitsWithTrace_frames (inputs : List SignedWord) :
    framePeak (wordsVisitsWithTrace inputs).2 ≤ 2*inputs.length+(BinaryStoredRowFrame.words inputs).length+7 := by
  induction inputs with
  | nil => simp [wordsVisitsWithTrace,framePeak,BinaryStoredRowFrame.words]
  | cons input rest ih =>
      have hl := wordVisitsWithTrace_frames input
      have hw := wordWithTrace_frames input
      have hlu := framePeak_under 2 (wordVisitsWithTrace input).2
      have hwu := framePeak_under 2 (wordWithTrace input).2
      have hru := framePeak_under 2 (wordsVisitsWithTrace rest).2
      simp only [wordsVisitsWithTrace,framePeak_append,framePeak,wordWithTrace_state,BinaryStoredRowFrame.words,
        List.length_append,List.length_cons]
      omega

-- One permanently reserved opcode workspace per coordinate, including the
-- actual arithmetic's retained internal buffers and held-input/control cells.
-- Array reservations include initial and every old/new full-capacity prefix
-- for BOTH the (word,work) array and the extracted word array. Fixed records
-- receive one extra unit per reserved region and four per coordinate.
def scalingTrace {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord) : Trace :=
  [.frames (n+8),.arrayAllocation (2*(n+1)^2+4*n+8)] ++
    (List.ofFn (fun j => Event.listAllocation (BinaryRationalOpcodeAllocation.opcodeStorage .mul budget (row.read j))))

def rescaleWithTrace {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord) :
    (FixedArrayTable n SignedWord × ℕ) × Trace :=
  let cells := FixedArrayTable.ofFn (fun j =>
    ((BinaryRationalOpcodeAllocation.applyWithAllocation .mul budget (row.read j)).1,
      (BinaryRationalOpcode.applyWithWork .mul budget (row.read j)).2))
  ((FixedArrayTable.ofFn (fun j => (cells.read j).1),∑ j,(cells.read j).2),scalingTrace budget row)

@[simp] theorem rescaleWithTrace_state {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord) :
    (rescaleWithTrace budget row).1 = rescaleWithWork budget row := by
  unfold rescaleWithTrace rescaleWithWork
  simp only [FixedArrayTable.read_ofFn,BinaryRationalOpcodeAllocation.applyWithAllocation_state,
    BinaryRationalOpcode.applyWithWork_state]

@[simp] theorem rescaleWithTrace_trace {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord) :
    (rescaleWithTrace budget row).2 = scalingTrace budget row := rfl

theorem listCells_ofFn (n : ℕ) (f : Fin n → ℕ) :
    listCells (List.ofFn (fun j => Event.listAllocation (f j))) = ∑ j, f j := by
  induction n with
  | zero => simp [listCells]
  | succ n ih =>
      rw [List.ofFn_succ]
      simp only [listCells,ih,Fin.sum_univ_succ]

theorem arraySlots_ofFn (n : ℕ) (f : Fin n → ℕ) :
    arraySlots (List.ofFn (fun j => Event.listAllocation (f j))) = 0 := by
  induction n with
  | zero => simp [arraySlots]
  | succ n ih =>
      rw [List.ofFn_succ]
      simp only [arraySlots,ih]

theorem scalingTrace_bound {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord) (W : ℕ)
    (hBudget : width budget ≤ W) (hRow : ∀ j,width (row.read j) ≤ W) :
    listCells (scalingTrace budget row) + arraySlots (scalingTrace budget row) ≤
      n*2000000*(W+2)^4+2*(n+1)^2+4*n+8 := by
  have hPrimitive : ∀ j,BinaryRationalOpcodeAllocation.opcodeStorage .mul budget (row.read j) ≤ 2000000*(W+2)^4 := by
    intro j
    exact (BinaryRationalOpcodeAllocation.opcodeStorage_bound .mul budget (row.read j)).trans
      (Nat.mul_le_mul_left 2000000 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le hBudget (hRow j)) 2) 4))
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hPrimitive j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hSum
  simp only [scalingTrace,listCells_append,arraySlots_append,listCells,arraySlots,listCells_ofFn,arraySlots_ofFn]
  nlinarith


theorem framePeak_ofFn (n : ℕ) (f : Fin n → ℕ) :
    framePeak (List.ofFn (fun j => Event.listAllocation (f j))) = 0 := by
  induction n with
  | zero => simp [framePeak]
  | succ n ih => rw [List.ofFn_succ]; simp only [framePeak,ih]

theorem scalingTrace_frames {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord) :
    framePeak (scalingTrace budget row) ≤ n+8 := by
  simp [scalingTrace,framePeak,framePeak_ofFn]

def normalized {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    FixedArrayTable n SignedWord × BinaryPRGOutputRun.Ledger :=
  BinaryPRGOutputRun.fixedSample prepared.request rich prepared.request.precision
    (coinBitBudget n prepared.request.precision) tables.outer.read tables.scalar.read tables.choice.read

theorem normalized_state {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    (normalized prepared rich tables).1 = (BinaryPRGCachedPrimitiveRun.sample prepared.request rich prepared.request.precision tables.flat).1 := by
  have h := BinaryPRGOutputRun.sample_state prepared.request rich prepared.request.precision tables.flat
  unfold BinaryPRGOutputRun.sample BinaryPRGOutputRun.innerSample at h
  rw [tables.outer_eq,tables.scalar_eq,tables.choice_eq] at h
  exact h

noncomputable def normalizedWidth {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) : ℕ :=
  1+2*normalizedHeight prepared.request prepared.request.precision

theorem normalized_width {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    ∀ j,width ((normalized prepared rich tables).1.read j) ≤ normalizedWidth prepared := by
  intro j
  rw [normalized_state]
  exact (normalizedSample_canonical prepared.request rich prepared.request.precision tables.flat j).2.trans
    (rationalWordWidth_of_height (normalizedSample_height prepared.request rich prepared.request.precision tables.flat j))

theorem budget_width {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) :
    width prepared.request.prepared.original.a ≤ normalizedWidth prepared :=
  prepared.request.valid.2.1.1.2.trans (rationalWordWidth_of_height (scale_height prepared.request prepared.request.precision))

theorem scaled_state {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    (rescaleWithWork prepared.request.prepared.original.a (normalized prepared rich tables).1).1 =
      (BinaryPRGCachedPrimitiveRun.originalSample prepared.request rich tables.flat).1 := by
  unfold BinaryPRGCachedPrimitiveRun.originalSample
  dsimp only
  rw [rescaleWithWork_state,normalized_state]

theorem scaled_width {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    ∀ j,width ((rescaleWithWork prepared.request.prepared.original.a (normalized prepared rich tables).1).1.read j) ≤ outputWidth prepared.request := by
  rw [scaled_state]
  exact originalSample_width prepared.request rich tables.flat

theorem words_length_bound (inputs : List SignedWord) (W : ℕ) (h : ∀ input ∈ inputs,width input ≤ W) :
    (BinaryStoredRowFrame.words inputs).length ≤ inputs.length*(4*W+3) := by
  have hs := storedSpines_bound inputs W h
  rw [BinaryStoredRowFrameWork.words_length]
  nlinarith

def outputWithTrace {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    (List Bool × BinaryPRGOutputRun.Ledger) × Trace :=
  let sampled := normalized prepared rich tables
  let scaled := rescaleWithTrace prepared.request.prepared.original.a sampled.1
  let inputs := List.ofFn scaled.1.1.read
  let framed := frameWithTrace prepared.header.bytes inputs
  let observedVisits := wordsVisitsWithTrace inputs
  let visits := observedVisits.1+2*n+prepared.header.bytes.length
  ((framed.1,{sampled.2 with scaling := scaled.1.2,coordinateFraming := visits}),
    scaled.2 ++ [.listAllocation n,.frames (n+8)] ++ under 2 framed.2 ++ [.listAllocation n] ++ under 2 observedVisits.2)

@[simp] theorem outputWithTrace_state {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    (outputWithTrace prepared rich tables).1 = BinaryPRGSeedBlockOutput.output prepared rich tables := by
  unfold outputWithTrace BinaryPRGSeedBlockOutput.output normalized
  simp only [frameWithTrace_state,rescaleWithTrace_state,wordsVisitsWithTrace_state]

noncomputable def suffixBound {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) : ℕ :=
  n*2000000*(normalizedWidth prepared+2)^4+2*(n+1)^2+6*n+8+
    prepared.header.bytes.length+7*n*(4*outputWidth prepared.request+3)

noncomputable def suffixFrames {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) : ℕ :=
  prepared.header.bytes.length+2*n+n*(4*outputWidth prepared.request+3)+15

theorem outputWithTrace_heap_bound {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    listCells (outputWithTrace prepared rich tables).2 + arraySlots (outputWithTrace prepared rich tables).2 ≤ suffixBound prepared := by
  let row := (rescaleWithWork prepared.request.prepared.original.a (normalized prepared rich tables).1).1
  let inputs := List.ofFn row.read
  have hScale := scalingTrace_bound prepared.request.prepared.original.a (normalized prepared rich tables).1
    (normalizedWidth prepared) (budget_width prepared) (normalized_width prepared rich tables)
  have hWords := words_length_bound inputs (outputWidth prepared.request)
    (by intro input hi; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi; exact scaled_width prepared rich tables j)
  have hFrame := frameWithTrace_cells prepared.header.bytes inputs
  simp only [inputs,List.length_ofFn] at hWords
  have hObserver := wordsVisitsWithTrace_cells inputs
  unfold outputWithTrace suffixBound
  simp only [rescaleWithTrace_state,rescaleWithTrace_trace,listCells_append,arraySlots_append,
    listCells,arraySlots,listCells_under,arraySlots_under,frameWithTrace_arrays,wordsVisitsWithTrace_arrays]
  change _ + _ ≤ _
  dsimp only [row,inputs] at hFrame hObserver hWords
  nlinarith


theorem outputWithTrace_frame_bound {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    framePeak (outputWithTrace prepared rich tables).2 ≤ suffixFrames prepared := by
  let row := (rescaleWithWork prepared.request.prepared.original.a (normalized prepared rich tables).1).1
  let inputs := List.ofFn row.read
  have hWords := words_length_bound inputs (outputWidth prepared.request)
    (by intro input hi; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi; exact scaled_width prepared rich tables j)
  have hScale := scalingTrace_frames prepared.request.prepared.original.a (normalized prepared rich tables).1
  have hFrame := frameWithTrace_frames prepared.header.bytes inputs
  have hObserved := wordsVisitsWithTrace_frames inputs
  have hFrameUnder := framePeak_under 2 (frameWithTrace prepared.header.bytes inputs).2
  have hObservedUnder := framePeak_under 2 (wordsVisitsWithTrace inputs).2
  simp only [inputs,List.length_ofFn] at hWords hFrame hObserved
  unfold outputWithTrace suffixFrames
  simp only [rescaleWithTrace_state,rescaleWithTrace_trace,framePeak_append,framePeak]
  dsimp only [inputs,row] at hFrameUnder hObservedUnder hFrame hObserved hWords
  omega

-- The original header, seed arrays, prepared request and preceding sampler
-- state are borrowed external storage. They are never inferred to be uniquely
-- owned, released, or frame-length bounded by this suffix theorem.
theorem output_all_prefix_reserved_heap {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) (borrowedPayload steps : ℕ) :
    retainedHeap borrowedPayload (outputWithTrace prepared rich tables).2 steps ≤ borrowedPayload+suffixBound prepared := by
  have hb := outputWithTrace_heap_bound prepared rich tables
  have hl := listCells_take_le (outputWithTrace prepared rich tables).2 steps
  have ha := arraySlots_take_le (outputWithTrace prepared rich tables).2 steps
  unfold retainedHeap
  omega

theorem output_all_prefix_controller_frames {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) (steps : ℕ) :
    framePeak ((outputWithTrace prepared rich tables).2.take steps) ≤ suffixFrames prepared :=
  (framePeak_take_le _ _).trans (outputWithTrace_frame_bound prepared rich tables)

-- Exact remaining representation obligation: the scalar work/cell counters,
-- OfFn indices/array capacities and source controller records require bounded
-- finite-binary records when interpreting these reservations physically.
-- These bounds identify the reached scalar fields; they do not certify the
-- allocation/GC behavior of Lean's Nat implementation or those records.
theorem output_counter_value_bound {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    (outputWithTrace prepared rich tables).1.2.scaling ≤ n*BinaryFactoryHeight.opcodeBound
      (normalizedHeight prepared.request prepared.request.precision) ∧
    (outputWithTrace prepared rich tables).1.2.coordinateFraming ≤
      4*n*(4*outputWidth prepared.request+3)+2*n+prepared.header.bytes.length := by
  have hScaling := requestScaling_bound prepared.request rich prepared.request.precision tables.flat
  have hWords := words_length_bound
    (List.ofFn (rescaleWithWork prepared.request.prepared.original.a (normalized prepared rich tables).1).1.read)
    (outputWidth prepared.request)
    (by intro word hi; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi; exact scaled_width prepared rich tables j)
  have hObserved := BinaryStoredRowFrameWork.wordsVisits_output_bound
    (List.ofFn (rescaleWithWork prepared.request.prepared.original.a (normalized prepared rich tables).1).1.read)
  rw [← normalized_state prepared rich tables] at hScaling
  unfold outputWithTrace
  simp only [rescaleWithTrace_state,wordsVisitsWithTrace_state]
  simp only [List.length_ofFn] at hWords
  refine ⟨hScaling,?_⟩
  have hObservedBound := hObserved.trans (Nat.mul_le_mul_left 4 hWords)
  calc
    _ ≤ 4*(n*(4*outputWidth prepared.request+3))+2*n+prepared.header.bytes.length := by omega
    _ = _ := by ring

end Blotto.BinaryPRGOutputLifetime
