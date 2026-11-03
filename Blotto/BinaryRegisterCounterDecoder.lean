import Blotto.BinaryRegisterCounterSpace
import Blotto.BinaryPayloadBufferMetadata

/-! Final counter decoding includes the actual small payload's buffer-copy,
length-counter and recursive index prices at the existing fixed 44*w profile.
The final subtraction has a concrete Boolean-decrement value refinement.
These are declared bit-price interpretations, not host runtime certificates. -/
namespace Blotto.BinaryRegisterCounterDecoder
open BinaryCarryCounter BinaryRegisterBooleanCount
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem metadata_quadratic (width : ℕ) : BinaryPayload.decoderMetadataBound 44 width ≤ 4096*(width+1)^2 := by
  have h1 : binaryWordWidth (width+1) ≤ width+2 := by
    have h := Nat.log2_le_self (width+1)
    unfold binaryWordWidth
    omega
  have h2 : binaryWordWidth (2*width+4) ≤ 2*width+5 := by
    have h := Nat.log2_le_self (2*width+4)
    unfold binaryWordWidth
    omega
  have hl := Nat.mul_le_mul_left (width+1) (Nat.add_le_add_right (Nat.mul_le_mul_left 46 h1) 1)
  have hi := Nat.mul_le_mul_left (2*width+1) (Nat.add_le_add_right (Nat.mul_le_mul_left 276 h2) 8)
  unfold BinaryPayload.decoderMetadataBound BinaryNatFrame.lengthMetadataBound
  norm_num only [Nat.reduceAdd,Nat.reduceMul]
  nlinarith only [hl,hi]

theorem counter_square (word : List Bool) : ((count word [true]).length+1)^2 ≤ 9*(word.length+1) := by
  have hCanon := count_canonical word [true] (show Canonical [true] from ⟨trivial,fun _ => rfl⟩)
  have hs := canonical_square_bound (count word [true]) hCanon
  rw [counter_value] at hs
  have hw := counter_width_linear word
  have hp : 1 ≤ word.length+1 := by omega
  nlinarith only [hs,hw,hp]

def metadataPrice (word : List Bool) : ℕ :=
  BinaryPayload.decoderMetadataBitWork (fun w => 44*w) (count word [true])

theorem metadata_price (word : List Bool) : metadataPrice word ≤ 36864*(word.length+1) := by
  have hm := BinaryPayload.decoderMetadataBitWork_bound (fun w => 44*w) 44 (fun _ => Nat.le_refl _) (count word [true])
  have hq := metadata_quadratic (count word [true]).length
  have hs := counter_square word
  change metadataPrice word ≤ _ at hm
  nlinarith only [hm,hq,hs]

theorem buffer_copy (word : List Bool) :
    BinaryPayload.bufferCopyWork (count word [true]).length 0 ≤ 6*(word.length+1) := by
  have hCanon := count_canonical word [true] (show Canonical [true] from ⟨trivial,fun _ => rfl⟩)
  have hs := canonical_square_bound (count word [true]) hCanon
  rw [counter_value] at hs
  have hw := counter_width_linear word
  rw [BinaryPayload.bufferCopyWork_eq]
  nlinarith only [hs,hw]

theorem index_width (word : List Bool) :
    BinaryPayload.indexMetadataWordWidth (count word [true]).toArray 0 (count word [true]).length ≤
      binaryWordWidth (4*(word.length+1)+4) := by
  have hw := counter_width_linear word
  simp only [BinaryPayload.indexMetadataWordWidth,List.size_toArray,Nat.add_zero]
  apply binaryWordWidth_mono
  omega

def finalPrice (word : List Bool) : ℕ := 44*((count word [true]).length+1)

theorem final_value (word : List Bool) :
    BinaryBigEndian.littleValue (BinaryStoredCountdown.predecessor (count word [true])) = word.length := by
  have hv := counter_value word
  change BinaryBigEndian.littleValue (count word [true]) = word.length+1 at hv
  have hp := BinaryStoredCountdown.predecessor_value (count word [true]) (by omega)
  omega

theorem final_boolean_price (word : List Bool) :
    (BooleanFreshSeedMeasured.predecessor (count word [true])).2 ≤ finalPrice word := by
  have h := BooleanFreshSeedMeasured.predecessor_bound (count word [true])
  unfold finalPrice
  omega

theorem final_price (word : List Bool) : finalPrice word ≤ 132*(word.length+1) := by
  have hw := counter_width_linear word
  unfold finalPrice
  omega

def completePrice (word : List Bool) : ℕ := sourcePrice word+metadataPrice word+finalPrice word

theorem complete_price (word : List Bool) : completePrice word ≤ 40000*(word.length+1) := by
  have hc := source_price word
  have hm := metadata_price word
  have hf := final_price word
  unfold completePrice
  omega

theorem old_price_dominates (word : List Bool) : completePrice word ≤ 40000*sourcePrice word := by
  exact (complete_price word).trans (Nat.mul_le_mul_left 40000 (BinaryRegisterCounterSpace.price_pays_length word))

theorem bits_word_refinement (word : List Bool) :
    BinaryRegisterBooleanCount.bits word =
      (BinaryBigEndian.littleValue (BinaryStoredCountdown.predecessor (count word [true])),
        value (count word [true])) := by
  rw [bits_record,final_value,counter_value]

theorem buffer_data (word : List Bool) :
    (NativeArrayConversionCore.pack (count word [true])).1 = (count word [true]).toArray :=
  NativeArrayConversionCore.pack_state _

def bufferVersions (word : List Bool) : ℕ := (NativeArrayConversionCore.pack (count word [true])).2.length

theorem buffer_versions (word : List Bool) : bufferVersions word = (count word [true]).length+1 :=
  NativeArrayConversionCore.pack_length _

def bufferReserve (word : List Bool) : ℕ := (count word [true]).length*bufferVersions word

theorem buffer_reserve (word : List Bool) : bufferReserve word ≤ 6*(word.length+1) := by
  have h := buffer_copy word
  rw [BinaryPayload.bufferCopyWork_eq] at h
  simpa only [bufferReserve,buffer_versions,Nat.mul_zero,Nat.zero_add] using h

theorem buffer_headers (word : List Bool) : bufferVersions word ≤ 3*(word.length+1) := by
  rw [buffer_versions]
  have hw := counter_width_linear word
  omega

open BinaryRationalNormalization BinaryRegisterMetadataPlan

def wordPrice (word : SignedWord) : ℕ := completePrice word.numerator+completePrice word.denominator

theorem word_payload (word : SignedWord) : wordPrice word ≤ 40000*(payload word).2 := by
  have hn := complete_price word.numerator
  have hd := complete_price word.denominator
  simp only [wordPrice,payload,bits_work]
  omega

theorem word_read (word : SignedWord) : wordPrice word ≤ 40000*readCharge word :=
  (word_payload word).trans (Nat.mul_le_mul_left 40000 (read_pays word))

theorem word_write (word : SignedWord) : wordPrice word ≤ 40000*writeCharge word :=
  (word_payload word).trans (Nat.mul_le_mul_left 40000 (write_pays word))

end Blotto.BinaryRegisterCounterDecoder
