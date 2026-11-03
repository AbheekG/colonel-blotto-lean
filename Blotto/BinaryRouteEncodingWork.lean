import Blotto.BinaryRouteSlot
import Blotto.BinaryFrameEncodingMetadata

/-! Route framing combines existing natural/rational encoder prices, their
metadata, the tag and actual left-prefix concatenation. Slot construction
retains conservative buffer work and repeated list-index bit accesses.
Concrete primitive/address implementations remain separate. -/

namespace Blotto.BinaryRouteFrame

def encodingWork {m : ℕ} (primitive : ℕ → ℕ) (route : GroupRoute m) : ℕ :=
  BinaryRatFrame.encodingBitWork primitive route.2 + BinaryRatFrame.encodingMetadataBitWork primitive route.2 +
    (match route.1 with
    | none => 0
    | some g => BinaryNatFrame.encodingBitWork primitive g.val + BinaryNatFrame.encodingMetadataBitWork primitive g.val +
        (BinaryNatFrame.encode g.val).length) + 1

def encodingBound (c P : ℕ) : ℕ :=
  (14 * c + 26) * (P + 1) ^ 2 + 3 * BinaryNatFrame.encodingMetadataBound c P + 2 * P + 4

theorem encodingWork_bound {m : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (route : GroupRoute m) (P : ℕ) (hPayload : routePayloadWordWidth route ≤ P) :
    encodingWork primitive route ≤ encodingBound c P := by
  have hRat : rationalWordWidth route.2 ≤ P := by unfold routePayloadWordWidth at hPayload; omega
  have hRatWork := BinaryRatFrame.encodingBitWork_uniform_bound primitive c hPrimitive route.2 P hRat
  have hRatMeta := BinaryRatFrame.encodingMetadataBitWork_bound primitive c hPrimitive route.2 P hRat
  unfold encodingWork
  cases ht : route.1 with
  | none =>
    dsimp only
    have hScale : (10 * c + 20) * (P + 1) ^ 2 ≤ (14 * c + 26) * (P + 1) ^ 2 :=
      Nat.mul_le_mul_right _ (by omega)
    have hRatFull := hRatWork.trans hScale
    unfold encodingBound
    omega
  | some g =>
    dsimp only
    have hIndex : binaryWordWidth g.val ≤ P := by
      unfold routePayloadWordWidth at hPayload
      rw [ht] at hPayload
      dsimp only at hPayload
      omega
    have hNat := BinaryNatFrame.encodingBitWork_uniform_bound primitive c hPrimitive g.val P hIndex
    have hNatMeta := (BinaryNatFrame.encodingMetadataBitWork_bound primitive c hPrimitive g.val).trans
      (BinaryNatFrame.encodingMetadataBound_mono c hIndex)
    have hBoth : BinaryRatFrame.encodingBitWork primitive route.2 + BinaryNatFrame.encodingBitWork primitive g.val ≤
        (14 * c + 26) * (P + 1) ^ 2 := (Nat.add_le_add hRatWork hNat).trans_eq (by ring)
    rw [BinaryNatFrame.encode_length]
    unfold encodingBound
    change BinaryRatFrame.encodingBitWork primitive route.2 + BinaryRatFrame.encodingMetadataBitWork primitive route.2 +
      (BinaryNatFrame.encodingBitWork primitive g.val + BinaryNatFrame.encodingMetadataBitWork primitive g.val +
        (2 * binaryWordWidth g.val + 1)) + 1 ≤
      (14 * c + 26) * (P + 1) ^ 2 + 3 * BinaryNatFrame.encodingMetadataBound c P + 2 * P + 4
    omega

end Blotto.BinaryRouteFrame

namespace Blotto.BinaryRouteSlot

def preparationWork {m : ℕ} (primitive : ℕ → ℕ) (route : GroupRoute m) (W : ℕ) : ℕ :=
  BinaryRouteFrame.encodingWork primitive route + BinaryPayload.bufferCopyWork W 0 + 2 * W +
    indexedLoopMetadataBitWork primitive 0 W + W * (W + 1)

def preparationBound (c P W : ℕ) : ℕ :=
  BinaryRouteFrame.encodingBound c P + 2 * W * (W + 1) + 2 * W + indexedLoopMetadataBound c W

theorem preparationWork_bound {m : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (route : GroupRoute m) (P W : ℕ) (hPayload : routePayloadWordWidth route ≤ P) :
    preparationWork primitive route W ≤ preparationBound c P W := by
  have hEncode := BinaryRouteFrame.encodingWork_bound primitive c hPrimitive route P hPayload
  have hLoop := indexedLoopMetadataBitWork_bound primitive c hPrimitive W
  unfold preparationWork preparationBound
  rw [BinaryPayload.bufferCopyWork_eq]
  simp only [Nat.mul_zero, Nat.zero_add]
  nlinarith

end Blotto.BinaryRouteSlot
