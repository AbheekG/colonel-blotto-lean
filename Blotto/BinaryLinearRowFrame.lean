import Blotto.BinaryStoredRowFrame
import Blotto.BinaryPRGOutputLifetime

/-! A suffix-passing stored-word serializer. The executable functions do not
compute lengths, indices, natural counters or traces. The separate interpreter
counts list cases, loads, constructors and calls at unit source cost. It is a
list-operation model, not a calibration of host references or fast arithmetic.
The header is prepared once. No rational-to-bits conversion is used in a draw. -/
namespace Blotto.BinaryLinearRowFrame
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryRationalOpcode
set_option autoImplicit false

def copyInto : List Bool → List Bool → List Bool
  | [],suffix => suffix
  | bit::rest,suffix => bit::copyInto rest suffix

def rulerInto : List Bool → List Bool → List Bool
  | [],suffix => suffix
  | _::rest,suffix => false::rulerInto rest suffix

def payloadInto (bits suffix : List Bool) : List Bool :=
  let copied := copyInto bits suffix
  rulerInto bits (true::copied)

def wordInto (word : SignedWord) (suffix : List Bool) : List Bool :=
  let denominator := payloadInto word.denominator suffix
  let numerator := payloadInto word.numerator denominator
  word.negative::numerator

def wordsInto : List SignedWord → List Bool → List Bool
  | [],suffix => suffix
  | word::rest,suffix => wordInto word (wordsInto rest suffix)

def frame (header : List Bool) (words : List SignedWord) : List Bool :=
  copyInto header (wordsInto words [])

theorem copy_data (bits suffix : List Bool) : copyInto bits suffix = bits++suffix := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [copyInto,List.cons_append,ih]

theorem ruler_data (bits suffix : List Bool) :
    rulerInto bits suffix = List.replicate bits.length false++suffix := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [rulerInto,List.length_cons,List.replicate_succ,List.cons_append,ih]

theorem payload_data (bits suffix : List Bool) :
    payloadInto bits suffix = BinaryStoredRowFrame.payload bits++suffix := by
  simp only [payloadInto,copy_data,ruler_data,BinaryStoredRowFrame.payload,List.append_assoc,List.cons_append]

theorem word_data (word : SignedWord) (suffix : List Bool) :
    wordInto word suffix = BinaryStoredRowFrame.word word++suffix := by
  simp only [wordInto,payload_data,BinaryStoredRowFrame.word,List.cons_append,List.append_assoc]

theorem words_data (words : List SignedWord) (suffix : List Bool) :
    wordsInto words suffix = BinaryStoredRowFrame.words words++suffix := by
  induction words with
  | nil => rfl
  | cons word rest ih => simp only [wordsInto,word_data,ih,BinaryStoredRowFrame.words,List.append_assoc]

theorem frame_data (header : List Bool) (words : List SignedWord) :
    frame header words = header++BinaryStoredRowFrame.words words := by
  simp only [frame,copy_data,words_data,List.append_nil]

theorem frame_read (words : List SignedWord) (h : ∀ word ∈ words, Valid word)
    (suffix : List Bool) :
    BinaryRatListFrame.readRow (frame (BinaryNatFrame.encode words.length) words++suffix) =
      some (words.length,words.map value,suffix) := by
  simp only [frame_data,List.append_assoc,BinaryRatListFrame.readRow,
    BinaryNatFrame.read_encode_append,Option.bind_some,BinaryStoredRowFrame.words_read words h,
    Option.map_some]

inductive Action where
  | inspect | load | cons | call
  deriving DecidableEq

structure Run where
  data : List Bool
  trace : List Action

def cells (trace : List Action) : ℕ := (trace.filter (· == .cons)).length

@[simp] theorem cells_append (a b : List Action) : cells (a++b) = cells a+cells b := by
  simp only [cells,List.filter_append,List.length_append]

def copyRun : List Bool → List Bool → Run
  | [],suffix => ⟨suffix,[.inspect]⟩
  | bit::rest,suffix =>
      let later := copyRun rest suffix
      ⟨bit::later.data,[.inspect,.load]++later.trace++[.cons]⟩

def rulerRun : List Bool → List Bool → Run
  | [],suffix => ⟨suffix,[.inspect]⟩
  | _::rest,suffix =>
      let later := rulerRun rest suffix
      ⟨false::later.data,[.inspect,.load]++later.trace++[.cons]⟩

def payloadRun (bits suffix : List Bool) : Run :=
  let copied := copyRun bits suffix
  let ruled := rulerRun bits (true::copied.data)
  ⟨ruled.data,[.call]++copied.trace++[.cons,.call]++ruled.trace⟩

def wordRun (word : SignedWord) (suffix : List Bool) : Run :=
  let denominator := payloadRun word.denominator suffix
  let numerator := payloadRun word.numerator denominator.data
  ⟨word.negative::numerator.data,[.load,.load]++denominator.trace++numerator.trace++[.load,.cons]⟩

def wordsRun : List SignedWord → List Bool → Run
  | [],suffix => ⟨suffix,[.inspect]⟩
  | word::rest,suffix =>
      let later := wordsRun rest suffix
      let first := wordRun word later.data
      ⟨first.data,[.inspect]++later.trace++[.load,.call]++first.trace⟩

def frameRun (header : List Bool) (words : List SignedWord) : Run :=
  let encoded := wordsRun words []
  let prefixed := copyRun header encoded.data
  ⟨prefixed.data,[.call]++encoded.trace++[.call]++prefixed.trace⟩

theorem copy_run_data (bits suffix : List Bool) : (copyRun bits suffix).data = copyInto bits suffix := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [copyRun,copyInto,ih]

theorem ruler_run_data (bits suffix : List Bool) : (rulerRun bits suffix).data = rulerInto bits suffix := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [rulerRun,rulerInto,ih]

theorem payload_run_data (bits suffix : List Bool) : (payloadRun bits suffix).data = payloadInto bits suffix := by
  simp only [payloadRun,payloadInto,ruler_run_data,copy_run_data]

theorem word_run_data (word : SignedWord) (suffix : List Bool) : (wordRun word suffix).data = wordInto word suffix := by
  simp only [wordRun,wordInto,payload_run_data]

theorem words_run_data (words : List SignedWord) (suffix : List Bool) : (wordsRun words suffix).data = wordsInto words suffix := by
  induction words with
  | nil => rfl
  | cons word rest ih => simp only [wordsRun,wordsInto,word_run_data,ih]

theorem frame_run_data (header : List Bool) (words : List SignedWord) : (frameRun header words).data = frame header words := by
  simp only [frameRun,frame,copy_run_data,words_run_data]

theorem copy_counts (bits suffix : List Bool) :
    (copyRun bits suffix).trace.length = 3*bits.length+1 ∧ cells (copyRun bits suffix).trace = bits.length := by
  induction bits with
  | nil => simp [copyRun,cells]
  | cons bit rest ih =>
      simp only [copyRun,List.length_append,List.length_cons,List.length_nil,cells_append] at *
      norm_num [cells] at *
      omega

theorem ruler_counts (bits suffix : List Bool) :
    (rulerRun bits suffix).trace.length = 3*bits.length+1 ∧ cells (rulerRun bits suffix).trace = bits.length := by
  induction bits with
  | nil => simp [rulerRun,cells]
  | cons bit rest ih =>
      simp only [rulerRun,List.length_append,List.length_cons,List.length_nil,cells_append] at *
      norm_num [cells] at *
      omega

theorem payload_counts (bits suffix : List Bool) :
    (payloadRun bits suffix).trace.length = 6*bits.length+5 ∧
      cells (payloadRun bits suffix).trace = 2*bits.length+1 := by
  have hc := copy_counts bits suffix
  have hr := ruler_counts bits (true::(copyRun bits suffix).data)
  simp only [payloadRun,List.length_append,List.length_cons,List.length_nil,cells_append]
  norm_num [cells] at *
  omega

theorem word_counts (word : SignedWord) (suffix : List Bool) :
    (wordRun word suffix).trace.length = 6*(word.numerator.length+word.denominator.length)+14 ∧
      cells (wordRun word suffix).trace = 2*(word.numerator.length+word.denominator.length)+3 := by
  have hd := payload_counts word.denominator suffix
  have hn := payload_counts word.numerator (payloadRun word.denominator suffix).data
  simp only [wordRun,List.length_append,List.length_cons,List.length_nil,cells_append]
  norm_num [cells] at *
  omega

def payloadSize (words : List SignedWord) : ℕ :=
  (words.map (fun word => word.numerator.length+word.denominator.length)).sum

theorem words_counts (words : List SignedWord) (suffix : List Bool) :
    (wordsRun words suffix).trace.length = 6*payloadSize words+17*words.length+1 ∧
      cells (wordsRun words suffix).trace = 2*payloadSize words+3*words.length := by
  induction words with
  | nil => simp [wordsRun,payloadSize,cells]
  | cons word rest ih =>
      have hw := word_counts word (wordsRun rest suffix).data
      simp only [wordsRun,payloadSize,List.map_cons,List.sum_cons,List.length_append,
        List.length_cons,List.length_nil,cells_append]
      simp only [payloadSize] at ih
      norm_num [cells] at *
      omega

theorem frame_counts (header : List Bool) (words : List SignedWord) :
    (frameRun header words).trace.length = 3*header.length+6*payloadSize words+17*words.length+4 ∧
      cells (frameRun header words).trace = header.length+2*payloadSize words+3*words.length := by
  have hw := words_counts words []
  have hc := copy_counts header (wordsRun words []).data
  simp only [frameRun,List.length_append,List.length_cons,List.length_nil,cells_append]
  norm_num [cells] at *
  omega

theorem payload_size_bound (words : List SignedWord) (W : ℕ) (h : ∀ word ∈ words, width word ≤ W) :
    payloadSize words ≤ 2*words.length*W := by
  induction words with
  | nil => simp [payloadSize]
  | cons word rest ih =>
      have hw := h word (by simp)
      have hn := Nat.le_max_left word.numerator.length word.denominator.length
      have hd := Nat.le_max_right word.numerator.length word.denominator.length
      have hr := ih (fun w hm => h w (by simp [hm]))
      simp only [width] at hw
      simp only [payloadSize,List.map_cons,List.sum_cons,List.length_cons] at *
      nlinarith

theorem frame_linear (header : List Bool) (words : List SignedWord) (W : ℕ)
    (h : ∀ word ∈ words, width word ≤ W) :
    (frameRun header words).trace.length ≤ 3*header.length+17*words.length*(W+1)+4 ∧
      cells (frameRun header words).trace ≤ header.length+words.length*(4*W+3) := by
  have hs := payload_size_bound words W h
  have hc := frame_counts header words
  constructor <;> nlinarith

theorem allocation_prefix (header : List Bool) (words : List SignedWord) (used : ℕ) :
    cells ((frameRun header words).trace.take used) ≤ cells (frameRun header words).trace := by
  have h := cells_append ((frameRun header words).trace.take used) ((frameRun header words).trace.drop used)
  rw [List.take_append_drop] at h
  omega

theorem frame_cells_exact (header : List Bool) (words : List SignedWord) :
    cells (frameRun header words).trace = (frame header words).length := by
  have h := (frame_counts header words).2
  have hw : (BinaryStoredRowFrame.words words).length = 2*payloadSize words+3*words.length := by
    clear h
    induction words with
    | nil => rfl
    | cons word rest ih =>
        simp only [BinaryStoredRowFrame.words,List.length_append,BinaryPRGOutputLifetime.word_length,
          List.length_cons,payloadSize,List.map_cons,List.sum_cons] at *
        omega
  simpa only [frame_data,List.length_append,hw,Nat.add_assoc] using h

end Blotto.BinaryLinearRowFrame
