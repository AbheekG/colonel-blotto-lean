import Blotto.BinaryStoredRowFrame

/-! Stored output encoding has a linear coordinate-payload spine allowance.
The recursive front append copies each encoded coordinate once; it does not
repeatedly copy an accumulated row prefix. Counts cover list length scans,
replication, local frame appends and row appends, with conservative extra copies.
Header integer encoding, logical array reads, addresses, counters and physical
allocator/stack/GC costs remain separate from this coordinate bit-cell ledger. -/

namespace Blotto.BinaryStoredRowFrameWork
open BinaryRationalNormalization BinaryStoredRowFrame

theorem payload_length (bits : List Bool) : (payload bits).length = 2 * bits.length + 1 := by
  simp only [payload, List.length_append, List.length_replicate, List.length_cons]
  omega

theorem word_length (input : SignedWord) :
    (word input).length = 2 * (input.numerator.length + input.denominator.length) + 3 := by
  simp only [word, List.length_cons, List.length_append, payload_length]
  omega

def storedSpines : List SignedWord → ℕ
  | [] => 0
  | input :: rest => input.numerator.length + input.denominator.length + storedSpines rest

theorem words_length (inputs : List SignedWord) :
    (words inputs).length = 2 * storedSpines inputs + 3 * inputs.length := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      simp only [words, List.length_append, word_length, storedSpines, List.length_cons, ih]
      omega

theorem row_length {n : ℕ} (input : FixedArrayTable n SignedWord) :
    (row input).length = 2 * binaryWordWidth n + 1 +
      2 * storedSpines (List.ofFn input.read) + 3 * n := by
  simp only [row, List.length_append, BinaryNatFrame.encode_length, words_length, List.length_ofFn]
  omega

def payloadVisits (bits : List Bool) : ℕ := 2 * bits.length + (payload bits).length + 1
def wordVisits (input : SignedWord) : ℕ :=
  payloadVisits input.numerator + payloadVisits input.denominator + (payload input.numerator).length + 1

def wordsVisits : List SignedWord → ℕ
  | [] => 0
  | input :: rest => wordVisits input + (word input).length + wordsVisits rest + 1

theorem payloadVisits_exact (bits : List Bool) : payloadVisits bits = 4 * bits.length + 2 := by
  rw [payloadVisits, payload_length]
  omega

theorem wordVisits_bound (input : SignedWord) :
    wordVisits input ≤ 6 * (input.numerator.length + input.denominator.length) + 6 := by
  simp only [wordVisits, payloadVisits_exact, payload_length]
  omega

theorem wordsVisits_bound (inputs : List SignedWord) :
    wordsVisits inputs ≤ 8 * storedSpines inputs + 10 * inputs.length := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      have hw := wordVisits_bound input
      simp only [wordsVisits, word_length, storedSpines, List.length_cons]
      omega

theorem wordsVisits_output_bound (inputs : List SignedWord) :
    wordsVisits inputs ≤ 4 * (words inputs).length := by
  have h := wordsVisits_bound inputs
  rw [words_length]
  omega

def rowCoordinateVisits {n : ℕ} (input : FixedArrayTable n SignedWord) : ℕ :=
  wordsVisits (List.ofFn input.read) + 2 * n + (BinaryNatFrame.encode n).length

theorem rowCoordinateVisits_bound {n : ℕ} (input : FixedArrayTable n SignedWord) :
    rowCoordinateVisits input ≤ 4 * (row input).length + 2 * n := by
  have h := wordsVisits_output_bound (List.ofFn input.read)
  unfold rowCoordinateVisits row
  rw [List.length_append]
  omega

end Blotto.BinaryStoredRowFrameWork
