import Blotto.BinaryPRGOriginalSampler
import Blotto.RationalPRGBinaryOutput

/-! Output framing copies stored numerator/denominator bits directly. It does
not enumerate bits from a rational value. A coordinate may use a nonminimal
payload width (including the empty zero numerator); the existing exact frame
reader accepts that width and returns the same rational value. Whole-row
readback is suffix preserving and transfers the original every-path budget. -/

namespace Blotto.BinaryStoredRowFrame
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryPRGPreparation

def payload (bits : List Bool) : List Bool := List.replicate bits.length false ++ true :: bits

theorem payload_read (bits suffix : List Bool) :
    BinaryNatFrame.read (payload bits ++ suffix) = some (BinaryPayload.decode bits, suffix) := by
  have ht : (bits ++ suffix).take bits.length = bits := List.take_left
  have hd : (bits ++ suffix).drop bits.length = suffix := List.drop_left
  have hl : bits.length ≤ (bits ++ suffix).length := by simp
  simp only [payload, List.append_assoc, List.cons_append, BinaryNatFrame.read,
    BinaryNatFrame.scanWidth_prefix, Nat.zero_add, Option.bind_some, ite_eq_left hl, ht, hd]

def word (input : SignedWord) : List Bool :=
  input.negative :: (payload input.numerator ++ payload input.denominator)

theorem word_read (input : SignedWord) (h : Valid input) (suffix : List Bool) :
    BinaryRatFrame.read (word input ++ suffix) = some (value input, suffix) := by
  have hd : BinaryPayload.decode input.denominator ≠ 0 := by
    rw [← BinaryBigEndian.littleValue_decode]
    exact ne_of_gt h
  simp only [word, List.cons_append, List.append_assoc, BinaryRatFrame.read,
    payload_read, Option.bind_some, ite_eq_right hd]
  rw [← BinaryBigEndian.littleValue_decode, ← BinaryBigEndian.littleValue_decode]
  rfl

def words : List SignedWord → List Bool
  | [] => []
  | input :: rest => word input ++ words rest

theorem words_read (inputs : List SignedWord) (h : ∀ input ∈ inputs, Valid input) (suffix : List Bool) :
    BinaryRatListFrame.read inputs.length (words inputs ++ suffix) = some (inputs.map value, suffix) := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      have ht : ∀ w ∈ rest, Valid w := fun w hw => h w (by simp [hw])
      simp only [words, List.append_assoc, List.length_cons, BinaryRatListFrame.read,
        word_read input (h input (by simp)) _, Option.bind_some, ih ht, List.map_cons, Option.map_some]

def row {n : ℕ} (input : FixedArrayTable n SignedWord) : List Bool :=
  BinaryNatFrame.encode n ++ words (List.ofFn input.read)

theorem row_read {n : ℕ} (input : FixedArrayTable n SignedWord)
    (h : ∀ j, Valid (input.read j)) (suffix : List Bool) :
    BinaryRatListFrame.readRow (row input ++ suffix) =
      some (n, List.ofFn (fun j => value (input.read j)), suffix) := by
  have hs := words_read (List.ofFn input.read)
    (by intro w hw; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw; exact h j) suffix
  simp only [List.length_ofFn, List.map_ofFn] at hs
  simp only [row, List.append_assoc, BinaryRatListFrame.readRow,
    BinaryNatFrame.read_encode_append, Option.bind_some, hs, Option.map_some]
  rfl

def richOutput {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : List Bool :=
  row (BinaryPRGOriginalSampler.richSample prepared h K bits)

def poorOutput {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : List Bool :=
  row (BinaryPRGOriginalSampler.poorSample prepared h K bits)

theorem richOutput_read {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (suffix : List Bool) :
    BinaryRatListFrame.readRow (richOutput prepared h K bits ++ suffix) =
      some (n, List.ofFn ((prepared.original.source h.2.2).richSample K bits), suffix) := by
  have hr := row_read (BinaryPRGOriginalSampler.richSample prepared h K bits)
    (fun j => (BinaryPRGOriginalSampler.richSample_canonical prepared h K bits j).1) suffix
  have he := BinaryPRGOriginalSampler.richSample_refines prepared h K bits
  change (fun j => value ((BinaryPRGOriginalSampler.richSample prepared h K bits).read j)) = _ at he
  simpa only [richOutput, he] using hr

theorem poorOutput_read {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (suffix : List Bool) :
    BinaryRatListFrame.readRow (poorOutput prepared h K bits ++ suffix) =
      some (n, List.ofFn ((prepared.original.source h.2.2).poorSample K bits), suffix) := by
  have hr := row_read (BinaryPRGOriginalSampler.poorSample prepared h K bits)
    (fun j => (BinaryPRGOriginalSampler.poorSample_canonical prepared h K bits j).1) suffix
  have he := BinaryPRGOriginalSampler.poorSample_refines prepared h K bits
  change (fun j => value ((BinaryPRGOriginalSampler.poorSample prepared h K bits).read j)) = _ at he
  simpa only [poorOutput, he] using hr

theorem output_budgets {n : ℕ} (prepared : Prepared n) (h : prepared.Valid) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    BinaryRatListFrame.FullBudgetList (value prepared.original.a)
      (List.ofFn ((prepared.original.source h.2.2).richSample K bits)) ∧
    BinaryRatListFrame.FullBudgetList (value prepared.original.b)
      (List.ofFn ((prepared.original.source h.2.2).poorSample K bits)) :=
  (prepared.original.source h.2.2).output_readback_budgets K bits

end Blotto.BinaryStoredRowFrame
