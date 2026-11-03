import Blotto.BinaryDyadicMidpoint

/-! Direct canonical dyadic midpoint construction from an existing Boolean
seed list. Odd numerator/power-of-two denominator coprimality avoids generic
GCD and division, while exact bytes equal the retained midpoint producer.
Linear Boolean/list-cell work is derived; address/control and full machine
composition remain separate. Numeric values/precision occur only in proofs. -/

namespace Blotto.BinaryDirectDyadicMidpoint
open BinaryRationalNormalization BinaryRationalOpcode

theorem trim_length_exact (bits : List Bool) (h : BinaryBigEndian.littleValue bits ≠ 0) :
    (BinaryCanonicalMagnitude.trim bits).length = binaryWordWidth (BinaryBigEndian.littleValue bits) := by
  have hu := BinaryBorrowWord.littleValue_bounds (BinaryCanonicalMagnitude.trim bits)
  rw [BinaryCanonicalMagnitude.trim_value] at hu
  have hlog := (Nat.log2_lt h).mpr hu
  have hl := BinaryCanonicalMagnitude.trim_wordWidth bits
  unfold binaryWordWidth at hlog hl ⊢
  omega

theorem trim_eq_of_value_eq (first second : List Bool)
    (h : BinaryBigEndian.littleValue first = BinaryBigEndian.littleValue second) :
    BinaryCanonicalMagnitude.trim first = BinaryCanonicalMagnitude.trim second := by
  by_cases hz : BinaryBigEndian.littleValue first = 0
  · rw [BinaryCanonicalMagnitude.trim_zero first hz,
      BinaryCanonicalMagnitude.trim_zero second (h.symm.trans hz)]
  · apply BinaryBorrowWord.littleValue_injective
    · rw [trim_length_exact first hz,trim_length_exact second (by omega),h]
    · simpa only [BinaryCanonicalMagnitude.trim_value] using h

theorem canonicalize_of_coprime (word : SignedWord) (hValid : Valid word) (hNonzero : BinaryBigEndian.littleValue word.numerator ≠ 0)
    (hCoprime : Nat.Coprime (BinaryBigEndian.littleValue word.numerator)
      (BinaryBigEndian.littleValue word.denominator)) : canonicalize word = trimWord word := by
  have hn := normalize_numerator_value word hValid
  have hd := normalize_denominator_value word hValid
  rw [hCoprime.gcd_eq_one,Nat.div_one] at hn hd
  have hSign : (normalize word).negative = word.negative := by
    rw [normalize_sign,(BinaryEuclideanGCD.nonzero_true_iff _).mpr (by omega),Bool.and_true]
  change SignedWord.mk (normalize word).negative (BinaryCanonicalMagnitude.trim (normalize word).numerator)
    (BinaryCanonicalMagnitude.trim (normalize word).denominator) =
    SignedWord.mk word.negative (BinaryCanonicalMagnitude.trim word.numerator)
      (BinaryCanonicalMagnitude.trim word.denominator)
  rw [hSign,trim_eq_of_value_eq _ _ hn,trim_eq_of_value_eq _ _ hd]

-- This list producer does not assemble a numerical precision or denominator.
def denominator (seed : List Bool) : List Bool := false :: (seed.map (fun _ => false) ++ [true])

theorem denominator_eq (seed : List Bool) : denominator seed = BinaryDyadicMidpoint.denominatorBits seed.length := by
  simp [denominator,BinaryDyadicMidpoint.denominatorBits,List.replicate_succ]

def raw (seed : List Bool) : SignedWord := ⟨false,true :: seed,denominator seed⟩

theorem raw_coprime (seed : List Bool) :
    Nat.Coprime (BinaryBigEndian.littleValue (raw seed).numerator)
      (BinaryBigEndian.littleValue (raw seed).denominator) := by
  have hc : Nat.Coprime (2 * BinaryBigEndian.littleValue seed + 1) 2 := by simp
  have hp := hc.pow_right (seed.length + 1)
  simpa only [raw,denominator_eq,BinaryDyadicMidpoint.denominatorBits_value,
    BinaryBigEndian.littleValue,ite_true] using hp

theorem raw_valid (seed : List Bool) : Valid (raw seed) := by
  change 0 < BinaryBigEndian.littleValue (denominator seed)
  rw [denominator_eq,BinaryDyadicMidpoint.denominatorBits_value]
  positivity

def sample (seed : List Bool) : SignedWord := trimWord (raw seed)

theorem sample_eq_canonicalize (seed : List Bool) : sample seed = canonicalize (raw seed) := by
  symm
  apply canonicalize_of_coprime _ (raw_valid seed) _ (raw_coprime seed)
  change 2 * BinaryBigEndian.littleValue seed + 1 ≠ 0
  omega

theorem sample_ofFn (K : ℕ) (bits : Fin K → Bool) :
    sample (List.ofFn bits) = BinaryDyadicMidpoint.sample K bits := by
  rw [sample_eq_canonicalize]
  congr 1
  unfold raw BinaryDyadicMidpoint.rawWord BinaryDyadicMidpoint.indexBits
  rw [denominator_eq,List.length_ofFn]

-- Actual output construction with an erased work annotation: Boolean map,
-- list append/cons and both existing linear trimming traversals. No GCD or
-- general division is invoked by the data producer.
def sampleWithWork (seed : List Bool) : SignedWord × ℕ :=
  let word := raw seed
  let numerator := BinaryCanonicalMagnitude.trimWithWork word.numerator
  let denominator := BinaryCanonicalMagnitude.trimWithWork word.denominator
  (⟨false,numerator.1,denominator.1⟩,3 * seed.length + 6 + numerator.2 + denominator.2)

theorem sampleWithWork_state (seed : List Bool) : (sampleWithWork seed).1 = sample seed := rfl

theorem sampleWithWork_bound (seed : List Bool) : (sampleWithWork seed).2 ≤ 20 * (seed.length + 2) := by
  have hn := BinaryCanonicalMagnitude.bitWork_bound (raw seed).numerator
  have hd := BinaryCanonicalMagnitude.bitWork_bound (raw seed).denominator
  simp only [raw,denominator_eq,BinaryDyadicMidpoint.denominatorBits_length,List.length_cons] at hn hd
  change 3 * seed.length + 6 + BinaryCanonicalMagnitude.bitWork (true :: seed) +
    BinaryCanonicalMagnitude.bitWork (denominator seed) ≤ _
  rw [denominator_eq]
  omega

theorem sampleWithWork_contract (K : ℕ) (bits : Fin K → Bool) :
    (sampleWithWork (List.ofFn bits)).1 = BinaryDyadicMidpoint.sample K bits ∧
      (sampleWithWork (List.ofFn bits)).2 ≤ 20 * (K + 2) := by
  exact ⟨sample_ofFn K bits,by simpa only [List.length_ofFn] using sampleWithWork_bound (List.ofFn bits)⟩

/-- Numeric length/index access here belongs to the old specification, not
    the direct Boolean-list producer. -/
theorem sample_specification (seed : List Bool) :
    sample seed = BinaryDyadicMidpoint.sample seed.length seed.get := by
  simpa only [List.ofFn_get] using sample_ofFn seed.length seed.get

theorem sample_contract (seed : List Bool) :
    value (sample seed) = dyadicMidpointSample seed.length seed.get ∧
    BinaryRationalEncoding.CanonicalWord (sample seed) ∧
    width (sample seed) ≤ seed.length + 2 ∧
    (sample seed).negative = false ∧
    0 < value (sample seed) ∧ value (sample seed) < 1 := by
  rw [sample_specification]
  exact ⟨BinaryDyadicMidpoint.sample_value _ _,BinaryDyadicMidpoint.sample_canonical _ _,
    BinaryDyadicMidpoint.sample_width _ _,BinaryDyadicMidpoint.sample_nonnegative_sign _ _,
    (BinaryDyadicMidpoint.sample_unit _ _).1,(BinaryDyadicMidpoint.sample_unit _ _).2⟩

end Blotto.BinaryDirectDyadicMidpoint
