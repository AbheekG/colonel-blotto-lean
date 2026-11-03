import Blotto.BinaryBalancedWordEncoder
import Blotto.BinarySequentialPayloadCost

/-! Actual cropped/shifted child operands have their own block heights.
Mask creation pays its output width, not just the encoded shift count.
The source profile includes scalar/control work and final width formation;
native bit primitives and physical memory remain separate interpretations. -/
namespace Blotto.BinaryBalancedWordEncodingCost
open BinaryBalancedWordEncoder
set_option autoImplicit false

def mergePrice (primitive : ℕ → ℕ) (length value : ℕ) : ℕ :=
  let low := length/2
  let power := 1 <<< low
  let mask := power-1
  let cropped := masked value low
  let high := value >>> low
  binaryWordWidth value+binaryWordWidth power+binaryWordWidth mask+binaryWordWidth cropped+binaryWordWidth high+
    primitive (low+1)+primitive (binaryWordWidth power)+
      primitive (max (binaryWordWidth value) (binaryWordWidth mask))+
        primitive (binaryWordWidth value+binaryWordWidth low)

theorem merge_price_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (length value : ℕ) (hLength : 1 < length) (hValue : value < 2^length) :
    mergePrice primitive length value ≤ (5+5*c)*length := by
  let low := length/2
  let high := length-low
  let power := 1 <<< low
  let mask := power-1
  have hLow : 0 < low := by dsimp [low]; omega
  have hHigh : 0 < high := by dsimp [high,low]; omega
  have hLowLE : low+1 ≤ length := by dsimp [low]; omega
  have hVal := binaryWordWidth_le_of_lt_pow (by omega : 0 < length) hValue
  have hPower : binaryWordWidth power ≤ low+1 := by
    apply binaryWordWidth_le_of_lt_pow (by omega : 0 < low+1)
    dsimp [power]
    rw [Nat.shiftLeft_eq,one_mul,pow_succ]
    nlinarith [Nat.two_pow_pos low]
  have hMask : binaryWordWidth mask ≤ low := by
    apply binaryWordWidth_le_of_lt_pow hLow
    dsimp [mask,power]
    rw [Nat.shiftLeft_eq,one_mul]
    have hp := Nat.two_pow_pos low
    omega
  have hCrop := binaryWordWidth_le_of_lt_pow hLow (masked_bound value low)
  have hShift := binaryWordWidth_le_of_lt_pow hHigh
    (shifted_bound length low value (by omega) hValue)
  have hLowWord : binaryWordWidth low ≤ low+1 := by
    have h := Nat.log2_le_self low
    unfold binaryWordWidth
    omega
  have hp1 := (hPrimitive (low+1)).trans (Nat.mul_le_mul_left c hLowLE)
  have hp2 := (hPrimitive (binaryWordWidth power)).trans (Nat.mul_le_mul_left c (hPower.trans hLowLE))
  have hp3 := (hPrimitive (max (binaryWordWidth value) (binaryWordWidth mask))).trans
    (Nat.mul_le_mul_left c (show max (binaryWordWidth value) (binaryWordWidth mask) ≤ length by omega))
  have hp4 := (hPrimitive (binaryWordWidth value+binaryWordWidth low)).trans
    (Nat.mul_le_mul_left c (show binaryWordWidth value+binaryWordWidth low ≤ 2*length by omega))
  change binaryWordWidth value+binaryWordWidth power+binaryWordWidth mask+
    binaryWordWidth (masked value low)+binaryWordWidth (value >>> low)+
    primitive (low+1)+primitive (binaryWordWidth power)+
    primitive (max (binaryWordWidth value) (binaryWordWidth mask))+
    primitive (binaryWordWidth value+binaryWordWidth low) ≤ (5+5*c)*length
  nlinarith [show low ≤ length by dsimp [low]; omega,show high ≤ length by dsimp [high,low]; omega]

def work (primitive : ℕ → ℕ) (length value : ℕ) : ℕ :=
  if length = 0 then BinarySequentialPayloadCost.scalarPrice primitive length else if length = 1 then
    3+primitive 2+BinarySequentialPayloadCost.scalarPrice primitive length
  else
    let low := length/2
    work primitive (length-low) (value >>> low)+work primitive low (masked value low)+
      mergePrice primitive length value+BinarySequentialPayloadCost.scalarPrice primitive length
termination_by length
decreasing_by all_goals omega

theorem work_majorant (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (length value capacity : ℕ) (hCapacity : length ≤ capacity) (hValue : value < 2^length) :
    work primitive length value ≤ (3+2*c)*length+(5+5*c)*BinaryPayload.mergeSize length+
      BinarySequentialPayloadCost.nodes length*BinarySequentialPayloadCost.scalarBound c capacity := by
  have hs := (BinarySequentialPayloadCost.scalar_price_bound primitive c hPrimitive length).trans
    (BinarySequentialPayloadCost.scalarBound_mono c hCapacity)
  unfold work
  split
  · rename_i hz
    subst length
    rw [BinaryPayload.mergeSize,ite_eq_left (show 0 ≤ 1 by decide),BinarySequentialPayloadCost.nodes,
      ite_eq_left (show 0 ≤ 1 by decide)]
    simpa only [Nat.mul_zero,Nat.zero_add,Nat.one_mul] using hs
  · split
    · rename_i hOne
      subst length
      have hp := hPrimitive 2
      rw [BinaryPayload.mergeSize,ite_eq_left (show 1 ≤ 1 by decide),BinarySequentialPayloadCost.nodes,
        ite_eq_left (show 1 ≤ 1 by decide)]
      simp only [Nat.mul_zero,Nat.add_zero,Nat.one_mul,Nat.mul_one]
      nlinarith only [hs,hp]
    · rename_i hZero hOne
      have hLength : 1 < length := by omega
      have hl := work_majorant primitive c hPrimitive (length/2) (masked value (length/2)) capacity
        (by omega) (masked_bound value (length/2))
      have hh := work_majorant primitive c hPrimitive (length-length/2) (value >>> (length/2)) capacity
        (by omega) (shifted_bound length (length/2) value (by omega) hValue)
      have hm := merge_price_bound primitive c hPrimitive length value hLength hValue
      dsimp only
      rw [BinaryPayload.mergeSize,ite_eq_right (by omega : ¬length ≤ 1),BinarySequentialPayloadCost.nodes,
        ite_eq_right (by omega : ¬length ≤ 1)]
      nlinarith only [hl,hh,hm,hs,show length/2+(length-length/2) = length by omega]
termination_by length
decreasing_by all_goals omega

def bitsWork (primitive : ℕ → ℕ) (value : ℕ) : ℕ :=
  let W := binaryWordWidth value
  3*primitive (2*W)+4*W+8+work primitive W value

theorem bits_work_majorant (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (value : ℕ) :
    let W := binaryWordWidth value
    bitsWork primitive value ≤ (6*c+4)*W+8+(3+2*c)*W+(5+5*c)*W*binaryWordWidth W+
      (2*W+1)*((12+4*c)*binaryWordWidth (W+2)+16) := by
  let W := binaryWordWidth value
  have hw := work_majorant primitive c hPrimitive W value W (Nat.le_refl _) (lt_pow_binaryWordWidth value)
  have hm := Nat.mul_le_mul_left (5+5*c) (BinaryPayload.mergeSize_word_bound W)
  have hn := Nat.mul_le_mul_right (BinarySequentialPayloadCost.scalarBound c W) (BinarySequentialPayloadCost.nodes_bound W)
  have hp := hPrimitive (2*W)
  unfold BinarySequentialPayloadCost.scalarBound at *
  change _ ≤ (6*c+4)*W+8+(3+2*c)*W+(5+5*c)*W*binaryWordWidth W+
    (2*W+1)*((12+4*c)*binaryWordWidth (W+2)+16)
  unfold bitsWork
  change 3*primitive (2*W)+4*W+8+work primitive W value ≤ _
  nlinarith only [hw,hm,hn,hp]

theorem bits_work_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (value : ℕ) :
    bitsWork primitive value ≤ 256*(c+1)*(binaryWordWidth value+1)*
      (binaryWordWidth (binaryWordWidth value+2)+1) := by
  let W := binaryWordWidth value
  let M := binaryWordWidth (W+2)
  have hw := bits_work_majorant primitive c hPrimitive value
  have hW : 1 ≤ W := binaryWordWidth_pos value
  have hM : 1 ≤ M := binaryWordWidth_pos (W+2)
  have hl := binaryWordWidth_mono (show W ≤ W+2 by omega)
  have hp := Nat.mul_le_mul_left ((5+5*c)*W) hl
  change bitsWork primitive value ≤ 256*(c+1)*(W+1)*(M+1)
  change bitsWork primitive value ≤ (6*c+4)*W+8+(3+2*c)*W+(5+5*c)*W*binaryWordWidth W+
    (2*W+1)*((12+4*c)*M+16) at hw
  change (5+5*c)*W*binaryWordWidth W ≤ (5+5*c)*W*M at hp
  have hWM : W ≤ W*M := by nlinarith only [hM]
  nlinarith only [hw,hp,hWM,hW,hM,Nat.zero_le (c*W*M),Nat.zero_le (c*W),Nat.zero_le (c*M)]

end Blotto.BinaryBalancedWordEncodingCost
