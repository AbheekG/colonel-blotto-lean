import Blotto.BinaryRationalRegisterProgram
import Blotto.PositiveBinaryWordParse
import Blotto.BinaryRatFrame

/-! Existing framed Boolean payloads and positive words supply actual binary
rational registers. Encoding never enumerates bits from a represented Nat or
Rat value: it keeps parsed numerator bits, reverses an existing positive word
when needed, then uses verified canonicalization. Parsing has exactly the
retained sign/numerator/positive-denominator frame semantics and suffix. -/

namespace Blotto.BinaryRationalEncoding
open BinaryRationalNormalization
open BinaryRationalOpcode
open scoped BigOperators

def CanonicalWord (word : SignedWord) : Prop :=
  Valid word ∧ width word ≤ rationalWordWidth (value word)

theorem zero_canonical : CanonicalWord zero := by
  refine ⟨zero_valid, ?_⟩
  rw [zero_value]
  change 1 ≤ rationalWordWidth (0 : ℚ)
  unfold rationalWordWidth
  omega

def fromPayload (negative : Bool) (numerator denominator : List Bool) : SignedWord :=
  canonicalize ⟨negative, numerator, denominator⟩

theorem fromPayload_value (negative : Bool) (numerator denominator : List Bool)
    (hDen : 0 < BinaryBigEndian.littleValue denominator) :
    value (fromPayload negative numerator denominator) =
      BinaryRatFrame.signedValue negative (BinaryBigEndian.littleValue numerator) /
        BinaryBigEndian.littleValue denominator := by
  rw [fromPayload, canonicalize_value (⟨negative, numerator, denominator⟩ : SignedWord) hDen]
  rfl

theorem fromPayload_canonical (negative : Bool) (numerator denominator : List Bool)
    (hDen : 0 < BinaryBigEndian.littleValue denominator) : CanonicalWord (fromPayload negative numerator denominator) := by
  refine ⟨canonicalize_valid _ hDen, ?_⟩
  have h := canonicalize_width (⟨negative, numerator, denominator⟩ : SignedWord) hDen
  rw [← canonicalize_value (⟨negative, numerator, denominator⟩ : SignedWord) hDen] at h
  exact h

def fromPositiveWords (negative : Bool) (numerator denominator : PositiveBinaryWord) : SignedWord :=
  fromPayload negative numerator.bits.reverse denominator.bits.reverse

theorem positiveWord_littleValue (word : PositiveBinaryWord) :
    BinaryBigEndian.littleValue word.bits.reverse = word.value := by
  rw [← BinaryBigEndian.value_reverse, List.reverse_reverse]
  rfl

theorem fromPositiveWords_value (negative : Bool) (numerator denominator : PositiveBinaryWord) :
    value (fromPositiveWords negative numerator denominator) =
      BinaryRatFrame.signedValue negative numerator.value / denominator.value := by
  have hd : 0 < BinaryBigEndian.littleValue denominator.bits.reverse := by
    rw [positiveWord_littleValue]
    exact denominator.value_pos
  rw [fromPositiveWords, fromPayload_value negative _ _ hd, positiveWord_littleValue, positiveWord_littleValue]

theorem fromPositiveWords_canonical (negative : Bool) (numerator denominator : PositiveBinaryWord) :
    CanonicalWord (fromPositiveWords negative numerator denominator) :=
  fromPayload_canonical negative _ _ (by rw [positiveWord_littleValue]; exact denominator.value_pos)

def readFrame : List Bool → Option (SignedWord × List Bool)
  | [] => none
  | negative :: rest =>
      (PositiveBinaryWord.readPayload rest).bind (fun first =>
        (PositiveBinaryWord.readPayload first.2).bind (fun second =>
          if BinaryEuclideanGCD.nonzero second.1 then
            some (fromPayload negative first.1 second.1, second.2) else none))

theorem readFrame_refines (frame : List Bool) :
    (readFrame frame).map (fun parsed => (value parsed.1, parsed.2)) = BinaryRatFrame.read frame := by
  cases frame with
  | nil => rfl
  | cons negative rest =>
      have hn := PositiveBinaryWord.readPayload_decode rest
      cases hFirst : PositiveBinaryWord.readPayload rest with
      | none =>
          rw [hFirst, Option.map_none] at hn
          simp only [readFrame, hFirst, Option.bind_none, Option.map_none, BinaryRatFrame.read, ← hn]
      | some first =>
          rcases first with ⟨numerator, suffix⟩
          rw [hFirst, Option.map_some] at hn
          have hd := PositiveBinaryWord.readPayload_decode suffix
          cases hSecond : PositiveBinaryWord.readPayload suffix with
          | none =>
              rw [hSecond, Option.map_none] at hd
              simp only [readFrame, hFirst, Option.bind_some, hSecond, Option.bind_none, Option.map_none,
                BinaryRatFrame.read, ← hn, ← hd]
          | some second =>
              rcases second with ⟨denominator, tail⟩
              rw [hSecond, Option.map_some] at hd
              simp only [readFrame, hFirst, Option.bind_some, hSecond, BinaryRatFrame.read, ← hn, ← hd]
              by_cases hNZ : BinaryEuclideanGCD.nonzero denominator = true
              · have hp := (BinaryEuclideanGCD.nonzero_true_iff denominator).mp hNZ
                have hv : BinaryPayload.decode denominator ≠ 0 := by
                  rw [← BinaryBigEndian.littleValue_decode]
                  exact ne_of_gt hp
                rw [ite_eq_left hNZ, ite_eq_right hv, Option.map_some]
                rw [fromPayload_value negative numerator denominator hp,
                  BinaryBigEndian.littleValue_decode, BinaryBigEndian.littleValue_decode]
              · have hz : BinaryBigEndian.littleValue denominator = 0 := by
                  apply (BinaryEuclideanGCD.nonzero_false_iff denominator).mp
                  cases he : BinaryEuclideanGCD.nonzero denominator <;> simp_all
                have hv : BinaryPayload.decode denominator = 0 := (BinaryBigEndian.littleValue_decode denominator).symm.trans hz
                rw [ite_eq_right hNZ, ite_eq_left hv]
                rfl

theorem readFrame_canonical (frame : List Bool) (word : SignedWord) (suffix : List Bool)
    (h : readFrame frame = some (word, suffix)) : CanonicalWord word := by
  cases frame with
  | nil => cases h
  | cons negative rest =>
      unfold readFrame at h
      dsimp only at h
      cases hFirst : PositiveBinaryWord.readPayload rest with
      | none => rw [hFirst, Option.bind_none] at h; cases h
      | some first =>
          rw [hFirst, Option.bind_some] at h
          cases hSecond : PositiveBinaryWord.readPayload first.2 with
          | none => rw [hSecond, Option.bind_none] at h; cases h
          | some second =>
              rw [hSecond, Option.bind_some] at h
              split at h
              · rename_i hDen
                cases Option.some.inj h
                exact fromPayload_canonical negative _ _ ((BinaryEuclideanGCD.nonzero_true_iff _).mp hDen)
              · cases h

theorem readFrame_sound (frame : List Bool) (word : SignedWord) (suffix : List Bool)
    (h : readFrame frame = some (word, suffix)) : BinaryRatFrame.read frame = some (value word, suffix) := by
  have he := readFrame_refines frame
  rw [h, Option.map_some] at he
  exact he.symm

theorem readFrame_complete (frame : List Bool) (q : ℚ) (suffix : List Bool)
    (h : BinaryRatFrame.read frame = some (q, suffix)) :
    ∃ word, readFrame frame = some (word, suffix) ∧ value word = q ∧ CanonicalWord word := by
  have he := readFrame_refines frame
  rw [h] at he
  cases hr : readFrame frame with
  | none => rw [hr, Option.map_none] at he; cases he
  | some parsed =>
      rcases parsed with ⟨word, tail⟩
      rw [hr, Option.map_some] at he
      have hp := Option.some.inj he
      have hq := congrArg Prod.fst hp
      have ht := congrArg Prod.snd hp
      change value word = q at hq
      change tail = suffix at ht
      subst tail
      exact ⟨word, rfl, hq, readFrame_canonical frame word suffix hr⟩

theorem readFrame_encode_append (q : ℚ) (suffix : List Bool) :
    ∃ word, readFrame (BinaryRatFrame.encode q ++ suffix) = some (word, suffix) ∧
      value word = q ∧ CanonicalWord word :=
  readFrame_complete _ q suffix (BinaryRatFrame.read_encode_append q suffix)

def canonicalRegisters (words : Array SignedWord) : Array SignedWord := words.map canonicalize

theorem canonicalRegisters_interpreted (words : Array SignedWord)
    (h : BinaryRationalRegisterProgram.ValidRegisters words) :
    BinaryRationalRegisterProgram.interpreted (canonicalRegisters words) = BinaryRationalRegisterProgram.interpreted words := by
  apply Array.ext
  · simp [BinaryRationalRegisterProgram.interpreted, canonicalRegisters]
  · intro i hi hj
    have hIndex : i < words.size := by simpa [BinaryRationalRegisterProgram.interpreted, canonicalRegisters] using hi
    have hValid := h i
    have hRead : BinaryRationalRegisterProgram.read words i = words[i]'hIndex := by
      simp [BinaryRationalRegisterProgram.read, Array.getD, hIndex]
    rw [hRead] at hValid
    simp only [BinaryRationalRegisterProgram.interpreted, canonicalRegisters, Array.getElem_map]
    exact canonicalize_value _ hValid

def registers (words : Array SignedWord) : Array SignedWord := words

theorem registers_interpreted (words : Array SignedWord) :
    BinaryRationalRegisterProgram.interpreted (registers words) = words.map value := rfl

end Blotto.BinaryRationalEncoding
