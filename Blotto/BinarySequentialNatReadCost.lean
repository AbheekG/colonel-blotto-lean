import Blotto.BinarySequentialPayloadCost
import Blotto.BinaryDecodedAggregateSize

/-! Actual reached scan and sequential decoder supply the natural reader's
source profile. No payload buffer, suffix-length pass or list copy is charged
because none occurs in this producer. The fixed wrapper allowance covers its
case/flag/option bookkeeping. Native primitive and memory prices stay separate. -/
namespace Blotto.BinarySequentialNatReadCost
open BinarySequentialPayloadDecoder
set_option autoImplicit false

def work (primitive : ℕ → ℕ) (frame : List Bool) : ℕ :=
  BinaryNatFrame.scanBitWork primitive 0 frame+
    match BinaryNatFrame.scanWidth 0 frame with
    | none => 4
    | some parsed => BinarySequentialPayloadCost.work primitive parsed.1 parsed.2+16

def price (c length : ℕ) : ℕ := (96+16*c)*(length+2)*binaryWordWidth (length+2)

theorem price_mono (c : ℕ) : Monotone (price c) := by
  intro a b hab
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right hab 2))
    (binaryWordWidth_mono (Nat.add_le_add_right hab 2))

theorem work_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (frame : List Bool) : work primitive frame ≤ price c frame.length := by
  let L := frame.length+2
  let W := binaryWordWidth L
  have hL : 2 ≤ L := by dsimp [L]; omega
  have hW : 1 ≤ W := binaryWordWidth_pos L
  have hLW : L ≤ L*W := by nlinarith only [hW]
  have hs := BinaryFrameLogDecodingCost.scan_bound primitive c hPrimitive 0 frame L (by dsimp [L]; omega)
  have hs' : BinaryNatFrame.scanBitWork primitive 0 frame ≤ (c+3)*L*W := by
    have hh := Nat.mul_le_mul (show frame.length+1 ≤ L by dsimp [L]; omega)
      (show (2+c)*W+1 ≤ (c+3)*W by nlinarith only [hW])
    nlinarith only [hs,hh]
  unfold work
  cases hScan : BinaryNatFrame.scanWidth 0 frame with
  | none =>
      dsimp only
      change _ ≤ (96+16*c)*L*W
      nlinarith only [hs',hLW,hL]
  | some parsed =>
      rcases parsed with ⟨length,bits⟩
      have hLength := consumed_width frame length bits hScan
      have hw := BinarySequentialPayloadCost.work_majorant primitive c hPrimitive length bits frame.length hLength
      have hm := BinaryPayload.mergeSize_word_bound length
      have hMerge : BinaryPayload.mergeSize length ≤ L*W := by
        have hh := Nat.mul_le_mul (show length ≤ L by dsimp [L]; omega)
          (binaryWordWidth_mono (show length ≤ L by dsimp [L]; omega))
        exact hm.trans hh
      have hM := Nat.mul_le_mul_left (4+2*c) hMerge
      have hn := BinarySequentialPayloadCost.nodes_bound length
      have hNodes : BinarySequentialPayloadCost.nodes length ≤ 2*L := by dsimp [L]; omega
      have hN := Nat.mul_le_mul_right (BinarySequentialPayloadCost.scalarBound c frame.length) hNodes
      unfold BinarySequentialPayloadCost.scalarBound at hN hw
      change BinarySequentialPayloadCost.work primitive length bits ≤
        length+(4+2*c)*BinaryPayload.mergeSize length+BinarySequentialPayloadCost.nodes length*((12+4*c)*W+16) at hw
      change BinarySequentialPayloadCost.nodes length*((12+4*c)*W+16) ≤ 2*L*((12+4*c)*W+16) at hN
      dsimp only
      change _ ≤ (96+16*c)*L*W
      have hSmall : length ≤ L := by dsimp [L]; omega
      nlinarith only [hs',hw,hM,hN,hSmall,hLW,hL]

theorem read_contract (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (frame : List Bool) : read frame = BinaryNatFrame.read frame ∧ work primitive frame ≤ price c frame.length :=
  ⟨read_refines frame,work_bound primitive c hPrimitive frame⟩

theorem read_width_consumed (frame : List Bool) (n : ℕ) (suffix : List Bool)
    (h : read frame = some (n,suffix)) : binaryWordWidth n+suffix.length ≤ frame.length := by
  rw [read_refines] at h
  exact BinaryDecodedAggregateSize.nat_width_consumed frame n suffix h

theorem encoded_contract (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (n : ℕ) (suffix : List Bool) :
    read (BinaryNatFrame.encode n++suffix) = some (n,suffix) ∧
      work primitive (BinaryNatFrame.encode n++suffix) ≤ price c (2*binaryWordWidth n+1+suffix.length) := by
  have hw := work_bound primitive c hPrimitive (BinaryNatFrame.encode n++suffix)
  rw [List.length_append,BinaryNatFrame.encode_length] at hw
  exact ⟨read_encode n suffix,hw⟩

end Blotto.BinarySequentialNatReadCost
