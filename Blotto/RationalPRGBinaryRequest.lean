import Blotto.RationalPRGBinaryInput
import Blotto.RationalPRGBinaryOutput
import Blotto.BinaryAccuracyFrame
import Blotto.BinaryAccuracyWordCorrespondence

/-! End-to-end bit interfaces parse and check a complete game/accuracy request,
require the exact bounded seed length, then emit the selected player's rational
row frame. The execution equivalence includes malformed-input rejection gates. -/

namespace Blotto.RationalPRGBinaryRequest

def encode {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput) : List Bool :=
  RationalPRGBinaryInput.encode i ++ BinaryAccuracyFrame.encode a

def read (bits : List Bool) : Option ((Σ n, RationalPRGOriginalInput n) × BinaryAccuracyInput × List Bool) :=
  (RationalPRGBinaryInput.readChecked bits).bind (fun game =>
    (BinaryAccuracyFrame.read game.2).map (fun accuracy => (game.1, accuracy.1, accuracy.2)))

def readWords (bits : List Bool) : Option ((Σ n, RationalPRGOriginalInput n) × BinaryAccuracyWords × List Bool) :=
  (RationalPRGBinaryInput.readChecked bits).bind (fun game =>
    (BinaryAccuracyWords.read game.2).map (fun accuracy => (game.1, accuracy.1, accuracy.2)))

theorem readWords_numeric_eq (bits : List Bool) :
    (readWords bits).map (fun parsed => (parsed.1, parsed.2.1.numeric, parsed.2.2)) = read bits := by
  unfold readWords read
  cases hg : RationalPRGBinaryInput.readChecked bits with
  | none => rfl
  | some game =>
    rcases game with ⟨input, rest⟩
    simp only [Option.bind_some]
    have h := BinaryAccuracyWords.read_numeric_eq rest
    cases hw : BinaryAccuracyWords.read rest with
    | none =>
      rw [hw, Option.map_none] at h
      rw [← h]
      rfl
    | some accuracy =>
      rcases accuracy with ⟨words, tail⟩
      rw [hw, Option.map_some] at h
      rw [← h]
      rfl

def seedTable (count : ℕ) (bits : List Bool) : Option (FixedArrayTable count Bool) :=
  if h : bits.length = count then some ⟨bits.toArray, by simpa using h⟩ else none

def runNumeric (rich : Bool) (request seed : List Bool) : Option (List Bool) :=
  (read request).bind (fun parsed =>
    if parsed.2.2 = [] then
      let K := parsed.2.1.precision
      (seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 K) seed).map (fun table =>
        if rich then parsed.1.2.richOutputBits K table.read else parsed.1.2.poorOutputBits K table.read)
    else none)

def run (rich : Bool) (request seed : List Bool) : Option (List Bool) :=
  (readWords request).bind (fun parsed =>
    if parsed.2.2 = [] then
      let K := parsed.2.1.precision
      (seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 K) seed).map (fun table =>
        if rich then parsed.1.2.richOutputBits K table.read else parsed.1.2.poorOutputBits K table.read)
    else none)

theorem run_refines (rich : Bool) (request seed : List Bool) : run rich request seed = runNumeric rich request seed := by
  have h := readWords_numeric_eq request
  cases hw : readWords request with
  | none =>
    rw [hw, Option.map_none] at h
    simp only [run, runNumeric, hw, ← h, Option.bind_none]
  | some parsed =>
    rcases parsed with ⟨game, words, tail⟩
    rw [hw, Option.map_some] at h
    simp only [run, runNumeric, hw, ← h, Option.bind_some]
    rw [words.precision_eq]

theorem read_encode_append {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput) (suffix : List Bool) :
    read (encode i a ++ suffix) = some ((⟨n, i⟩ : Σ n, RationalPRGOriginalInput n), a, suffix) := by
  simp only [read, encode, List.append_assoc, RationalPRGBinaryInput.readChecked_encode_append,
    Option.bind_some, BinaryAccuracyFrame.read_encode_append, Option.map_some]

theorem seedTable_ofFn {count : ℕ} (bits : Fin count → Bool) :
    seedTable count (List.ofFn bits) = some (FixedArrayTable.ofFn bits) := by
  unfold seedTable
  rw [dite_eq_left (show (List.ofFn bits).length = count by simp)]
  congr 1
  cases h : FixedArrayTable.ofFn bits with
  | mk data size =>
    have hData : data = (List.ofFn bits).toArray := by
      have he := congrArg FixedArrayTable.data h
      simpa [FixedArrayTable.ofFn] using he.symm
    cases hData
    rfl

theorem run_encode {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n a.precision) → Bool) :
    run rich (encode i a) (List.ofFn bits) =
      some (if rich then i.richOutputBits a.precision bits else i.poorOutputBits a.precision bits) := by
  rw [run_refines]
  have hRead := read_encode_append i a []
  have hBits : (FixedArrayTable.ofFn bits).read = bits := funext (fun j => FixedArrayTable.read_ofFn bits j)
  simp only [List.append_nil] at hRead
  simp only [runNumeric, hRead, Option.bind_some, ite_true, seedTable_ofFn, Option.map_some, hBits]

theorem seedTable_wrong_length (count : ℕ) (bits : List Bool) (h : bits.length ≠ count) : seedTable count bits = none := by
  rw [seedTable, dite_eq_right h]

def ReturnedBudget (count : ℕ) (B : ℚ) (frame : List Bool) : Prop :=
  ∃ values, BinaryRatListFrame.readRow frame = some (count, values, []) ∧ BinaryRatListFrame.FullBudgetList B values

theorem run_returned_budget {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n a.precision) → Bool) (frame : List Bool)
    (h : run rich (encode i a) (List.ofFn bits) = some frame) : ReturnedBudget n (if rich then i.a else i.b) frame := by
  rw [run_encode] at h
  cases rich with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h ⊢
    cases Option.some.inj h
    exact ⟨List.ofFn (i.poorSample a.precision bits), by simpa using i.poorOutput_readback a.precision bits [],
      (i.output_readback_budgets a.precision bits).2⟩
  | true =>
    simp only [ite_true] at h ⊢
    cases Option.some.inj h
    exact ⟨List.ofFn (i.richSample a.precision bits), by simpa using i.richOutput_readback a.precision bits [],
      (i.output_readback_budgets a.precision bits).1⟩

end Blotto.RationalPRGBinaryRequest
