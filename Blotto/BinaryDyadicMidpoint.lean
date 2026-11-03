import Blotto.BinaryRationalEncoding
import Blotto.DyadicMidpointHeight

/-! Native stored Boolean midpoint words. Input zero is the least significant
index bit. The producer copies those input bits after an odd low bit, builds a
power-of-two denominator by Boolean list constructors, and canonicalizes using
verified Boolean GCD, division and trimming. Rational values are specifications
only; no represented Nat or Rat is encoded at runtime. The work observer is the
existing abstract Boolean/list-cell model, not a physical compiler cost. -/

namespace Blotto.BinaryDyadicMidpoint
open BinaryRationalNormalization BinaryRationalOpcode BinaryRationalEncoding

-- Existing input bits are copied in their original, least-significant-first order.
def indexBits (K : ℕ) (bits : Fin K → Bool) : List Bool := List.ofFn bits

theorem indexBits_length (K : ℕ) (bits : Fin K → Bool) : (indexBits K bits).length = K :=
  List.length_ofFn

theorem indexBits_value (K : ℕ) (bits : Fin K → Bool) :
    BinaryBigEndian.littleValue (indexBits K bits) = (bitIndex K bits).val := by
  induction K with
  | zero => simp [indexBits, bitIndex, BinaryBigEndian.littleValue]
  | succ K ih =>
      rw [indexBits, List.ofFn_succ]
      change 2 * BinaryBigEndian.littleValue (indexBits K (Fin.tail bits)) +
        (if bits 0 then 1 else 0) = _
      rw [ih]
      rfl

def denominatorBits (K : ℕ) : List Bool := List.replicate (K + 1) false ++ [true]

theorem denominatorBits_length (K : ℕ) : (denominatorBits K).length = K + 2 := by
  simp [denominatorBits]

theorem falseBits_value (n : ℕ) : BinaryBigEndian.littleValue (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, BinaryBigEndian.littleValue, ih]

theorem denominatorBits_value (K : ℕ) : BinaryBigEndian.littleValue (denominatorBits K) = 2 ^ (K + 1) := by
  rw [denominatorBits, BinaryWordHighBit.littleValue_append, falseBits_value]
  simp [BinaryBigEndian.littleValue]

def rawWord (K : ℕ) (bits : Fin K → Bool) : SignedWord :=
  ⟨false, true :: indexBits K bits, denominatorBits K⟩

theorem rawWord_numerator (K : ℕ) (bits : Fin K → Bool) :
    BinaryBigEndian.littleValue (rawWord K bits).numerator = 2 * (bitIndex K bits).val + 1 := by
  simp only [rawWord, BinaryBigEndian.littleValue, indexBits_value, ite_true]

theorem rawWord_denominator (K : ℕ) (bits : Fin K → Bool) :
    BinaryBigEndian.littleValue (rawWord K bits).denominator = 2 ^ (K + 1) :=
  denominatorBits_value K

theorem rawWord_valid (K : ℕ) (bits : Fin K → Bool) : Valid (rawWord K bits) := by
  change 0 < BinaryBigEndian.littleValue (denominatorBits K)
  rw [denominatorBits_value]
  exact Nat.two_pow_pos _

theorem rawWord_value (K : ℕ) (bits : Fin K → Bool) :
    value (rawWord K bits) = dyadicMidpointSample K bits := by
  unfold value
  change (BinaryBigEndian.littleValue (rawWord K bits).numerator : ℚ) /
    BinaryBigEndian.littleValue (rawWord K bits).denominator = _
  rw [rawWord_numerator, rawWord_denominator, dyadicMidpointSample_refines]
  simp only [dyadicMidpointSampleReference, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  congr 1
  ring

theorem rawWord_width (K : ℕ) (bits : Fin K → Bool) : width (rawWord K bits) = K + 2 := by
  simp only [width, rawWord, List.length_cons, indexBits_length, denominatorBits_length]
  omega

def sample (K : ℕ) (bits : Fin K → Bool) : SignedWord := canonicalize (rawWord K bits)

theorem sample_value (K : ℕ) (bits : Fin K → Bool) : value (sample K bits) = dyadicMidpointSample K bits :=
  (canonicalize_value _ (rawWord_valid K bits)).trans (rawWord_value K bits)

theorem sample_canonical (K : ℕ) (bits : Fin K → Bool) : CanonicalWord (sample K bits) := by
  refine ⟨canonicalize_valid _ (rawWord_valid K bits), ?_⟩
  have h := canonicalize_width (rawWord K bits) (rawWord_valid K bits)
  rw [← canonicalize_value (rawWord K bits) (rawWord_valid K bits)] at h
  exact h

theorem sample_width (K : ℕ) (bits : Fin K → Bool) : width (sample K bits) ≤ K + 2 := by
  have hn := BinaryCanonicalMagnitude.trim_length (normalize (rawWord K bits)).numerator
  have hd := BinaryCanonicalMagnitude.trim_length (normalize (rawWord K bits)).denominator
  rw [(normalize_lengths (rawWord K bits)).1] at hn
  rw [(normalize_lengths (rawWord K bits)).2] at hd
  change max (BinaryCanonicalMagnitude.trim (normalize (rawWord K bits)).numerator).length
    (BinaryCanonicalMagnitude.trim (normalize (rawWord K bits)).denominator).length ≤ K + 2
  apply max_le
  · apply hn.trans
    simp only [rawWord, List.length_cons, indexBits_length]
    omega
  · apply hd.trans
    simp only [rawWord, denominatorBits_length]
    exact le_rfl

theorem sample_nonnegative_sign (K : ℕ) (bits : Fin K → Bool) : (sample K bits).negative = false := by
  change (normalize (rawWord K bits)).negative = false
  rw [normalize_sign]
  rfl

theorem sample_coprime (K : ℕ) (bits : Fin K → Bool) :
    Nat.Coprime (BinaryBigEndian.littleValue (sample K bits).numerator)
      (BinaryBigEndian.littleValue (sample K bits).denominator) :=
  canonicalize_coprime _ (rawWord_valid K bits)

theorem sample_unit (K : ℕ) (bits : Fin K → Bool) : 0 < value (sample K bits) ∧ value (sample K bits) < 1 := by
  rw [sample_value]
  have h := dyadicMidpointSample_bounds K bits
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

-- Four cells/read operations per copied input and the constant framing payload
-- conservatively cover Boolean construction; canonicalization is charged by
-- its verified observer, including all GCD/division and trimming passes.
def sampleWithWork (K : ℕ) (bits : Fin K → Bool) : SignedWord × ℕ :=
  let normalized := canonicalizeWithWork (rawWord K bits)
  (normalized.1, 4 * K + 8 + normalized.2)

theorem sampleWithWork_state (K : ℕ) (bits : Fin K → Bool) : (sampleWithWork K bits).1 = sample K bits := rfl

theorem sampleWithWork_bound (K : ℕ) (bits : Fin K → Bool) :
    (sampleWithWork K bits).2 ≤ 180 * (K + 3) ^ 3 := by
  have h := canonicalizeWithWork_bound (rawWord K bits)
  rw [rawWord_width] at h
  change 4 * K + 8 + (canonicalizeWithWork (rawWord K bits)).2 ≤ _
  have hp : K + 3 ≤ (K + 3) ^ 3 := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < K + 3) (by omega : 1 ≤ 3))
  nlinarith

theorem sampleWithWork_contract (K : ℕ) (bits : Fin K → Bool) :
    value (sampleWithWork K bits).1 = dyadicMidpointSample K bits ∧
      CanonicalWord (sampleWithWork K bits).1 ∧
      width (sampleWithWork K bits).1 ≤ K + 2 ∧
      (sampleWithWork K bits).1.negative = false ∧
      (sampleWithWork K bits).2 ≤ 180 * (K + 3) ^ 3 :=
  ⟨sample_value K bits, sample_canonical K bits, sample_width K bits,
    sample_nonnegative_sign K bits, sampleWithWork_bound K bits⟩

end Blotto.BinaryDyadicMidpoint
