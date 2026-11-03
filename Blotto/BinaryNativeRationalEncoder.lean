import Blotto.BinaryBalancedWordEncodingCost
import Blotto.BinaryLinearRowFrame

/-! Native reduced rationals are converted directly to stored signed words by
the balanced encoder, then framed by the linear suffix serializer. No Boolean
GCD/normalization or per-bit wide-word indexing is executed by this path.
Source bit prices use the explicit linear primitive profile. -/
namespace Blotto.BinaryNativeRationalEncoder
open BinaryRationalNormalization
set_option autoImplicit false

def word (q : ℚ) : SignedWord :=
  ⟨decide (q.num < 0),BinaryBalancedWordEncoder.bits q.num.natAbs,BinaryBalancedWordEncoder.bits q.den⟩

theorem bits_value (n : ℕ) : BinaryBigEndian.littleValue (BinaryBalancedWordEncoder.bits n) = n := by
  rw [BinaryBigEndian.littleValue_decode,BinaryBalancedWordEncoder.bits_decode]

theorem word_value (q : ℚ) : value (word q) = q := by
  unfold value word
  rw [bits_value,bits_value]
  change BinaryRatFrame.signedValue (decide (q.num < 0)) q.num.natAbs/(q.den : ℚ) = q
  rw [BinaryRatFrame.signedValue_natAbs,Rat.num_div_den]

theorem word_valid (q : ℚ) : BinaryRationalOpcode.Valid (word q) := by
  change 0 < BinaryBigEndian.littleValue (BinaryBalancedWordEncoder.bits q.den)
  rw [bits_value]
  exact q.den_pos

theorem word_width (q : ℚ) : width (word q) ≤ rationalWordWidth q := by
  simp only [word,width,BinaryBalancedWordEncoder.bits_length]
  unfold rationalWordWidth
  omega

theorem word_canonical (q : ℚ) : BinaryRationalEncoding.CanonicalWord (word q) :=
  ⟨word_valid q,by rw [word_value]; exact word_width q⟩

theorem payload_bits (n : ℕ) : BinaryStoredRowFrame.payload (BinaryBalancedWordEncoder.bits n) = BinaryNatFrame.encode n := by
  simp only [BinaryStoredRowFrame.payload,BinaryBalancedWordEncoder.bits_data,BinaryPayload.bits_length,BinaryNatFrame.encode]

def into (q : ℚ) (suffix : List Bool) : List Bool := BinaryLinearRowFrame.wordInto (word q) suffix

theorem into_data (q : ℚ) (suffix : List Bool) : into q suffix = BinaryRatFrame.encode q++suffix := by
  simp only [into,BinaryLinearRowFrame.word_data,BinaryStoredRowFrame.word,word,payload_bits,BinaryRatFrame.encode]

theorem into_read (q : ℚ) (suffix : List Bool) : BinaryRatFrame.read (into q suffix) = some (q,suffix) := by
  rw [into_data,BinaryRatFrame.read_encode_append]

theorem into_length (q : ℚ) (suffix : List Bool) : (into q suffix).length = 2*rationalWordWidth q+1+suffix.length := by
  rw [into_data,List.length_append,BinaryRatFrame.encode_length]

def wordWork (primitive : ℕ → ℕ) (q : ℚ) : ℕ :=
  BinaryBalancedWordEncodingCost.bitsWork primitive q.num.natAbs+
    BinaryBalancedWordEncodingCost.bitsWork primitive q.den+3*primitive (rationalWordWidth q+1)+4*rationalWordWidth q+16

theorem word_work_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (q : ℚ) :
    wordWork primitive q ≤ 512*(c+1)*(rationalWordWidth q+1)*(binaryWordWidth (rationalWordWidth q+2)+1) := by
  let A := binaryWordWidth q.num.natAbs
  let B := binaryWordWidth q.den
  let Q := rationalWordWidth q
  let M := binaryWordWidth (Q+2)+1
  have ha := BinaryBalancedWordEncodingCost.bits_work_bound primitive c hPrimitive q.num.natAbs
  have hb := BinaryBalancedWordEncodingCost.bits_work_bound primitive c hPrimitive q.den
  have hA : A ≤ Q := by dsimp [A,Q,rationalWordWidth]; omega
  have hB : B ≤ Q := by dsimp [B,Q,rationalWordWidth]; omega
  have hpa := Nat.mul_le_mul_left (256*(c+1)*(A+1))
    (Nat.add_le_add_right (binaryWordWidth_mono (Nat.add_le_add_right hA 2)) 1)
  have hpb := Nat.mul_le_mul_left (256*(c+1)*(B+1))
    (Nat.add_le_add_right (binaryWordWidth_mono (Nat.add_le_add_right hB 2)) 1)
  change BinaryBalancedWordEncodingCost.bitsWork primitive q.num.natAbs ≤ 256*(c+1)*(A+1)*(binaryWordWidth (A+2)+1) at ha
  change BinaryBalancedWordEncodingCost.bitsWork primitive q.den ≤ 256*(c+1)*(B+1)*(binaryWordWidth (B+2)+1) at hb
  change 256*(c+1)*(A+1)*(binaryWordWidth (A+2)+1) ≤ 256*(c+1)*(A+1)*M at hpa
  change 256*(c+1)*(B+1)*(binaryWordWidth (B+2)+1) ≤ 256*(c+1)*(B+1)*M at hpb
  have hSum : A+B+2 = Q+1 := by dsimp [A,B,Q,rationalWordWidth]; omega
  have hPrices : 256*(c+1)*(A+1)*M+256*(c+1)*(B+1)*M = 256*(c+1)*(Q+1)*M := by
    calc
      _ = 256*(c+1)*(A+B+2)*M := by ring
      _ = _ := by rw [hSum]
  have hWords := (Nat.add_le_add (ha.trans hpa) (hb.trans hpb)).trans_eq hPrices
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hQM : Q+1 ≤ (Q+1)*M := by nlinarith only [hM]
  have hp := hPrimitive (Q+1)
  have he := Nat.mul_le_mul_left (3*c+20) hQM
  have hc := Nat.mul_le_mul_right ((Q+1)*M) (show 3*c+20 ≤ 256*(c+1) by omega)
  have hExtra : 3*primitive (Q+1)+4*Q+16 ≤ 256*(c+1)*(Q+1)*M := by nlinarith only [hp,he,hc]
  change wordWork primitive q ≤ 512*(c+1)*(Q+1)*M
  unfold wordWork
  change _ ≤ 512*(c+1)*(Q+1)*M
  change 3*primitive (rationalWordWidth q+1)+4*rationalWordWidth q+16 ≤ _ at hExtra
  nlinarith only [hWords,hExtra]

def intoWork (primitive : ℕ → ℕ) (q : ℚ) (suffix : List Bool) : ℕ :=
  wordWork primitive q+(BinaryLinearRowFrame.wordRun (word q) suffix).trace.length

theorem into_work_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (q : ℚ) (suffix : List Bool) :
    intoWork primitive q suffix ≤ 1024*(c+1)*(rationalWordWidth q+1)*(binaryWordWidth (rationalWordWidth q+2)+1) := by
  let Q := rationalWordWidth q
  let M := binaryWordWidth (Q+2)+1
  have hw := word_work_bound primitive c hPrimitive q
  have hs := (BinaryLinearRowFrame.word_counts (word q) suffix).1
  simp only [word,BinaryBalancedWordEncoder.bits_length] at hs
  have hSerial : (BinaryLinearRowFrame.wordRun (word q) suffix).trace.length ≤ 6*Q+14 := by
    dsimp [Q,rationalWordWidth]
    simp only [word]
    omega
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hQM : Q+1 ≤ (Q+1)*M := by nlinarith only [hM]
  have he := Nat.mul_le_mul_left 20 hQM
  have hc := Nat.mul_le_mul_right ((Q+1)*M) (show 20 ≤ 512*(c+1) by omega)
  have hSerial' : (BinaryLinearRowFrame.wordRun (word q) suffix).trace.length ≤ 512*(c+1)*(Q+1)*M := by
    nlinarith only [hSerial,he,hc]
  change wordWork primitive q ≤ 512*(c+1)*(Q+1)*M at hw
  change intoWork primitive q suffix ≤ 1024*(c+1)*(Q+1)*M
  unfold intoWork
  nlinarith only [hw,hSerial']

theorem into_contract (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (q : ℚ) (suffix : List Bool) :
    BinaryRatFrame.read (into q suffix) = some (q,suffix) ∧
      intoWork primitive q suffix ≤ 1024*(c+1)*(rationalWordWidth q+1)*(binaryWordWidth (rationalWordWidth q+2)+1) :=
  ⟨into_read q suffix,into_work_bound primitive c hPrimitive q suffix⟩

end Blotto.BinaryNativeRationalEncoder
