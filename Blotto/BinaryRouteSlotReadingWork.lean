import Blotto.BinaryRouteDecoderMetadata
import Blotto.FixedRegionAddressWork

/-! One route read fetches its entire fixed slot, constructs its bit list,
then follows actual route parsing and metadata branches. Bounds are valid for
all slot contents. Address formation/allocation/primitive realization remain
separate; no validity assumption is used to price malformed reads. -/

namespace Blotto.BinaryRouteSlot
open scoped BigOperators

def fetchWork {n W : ℕ} (primitive : ℕ → ℕ) (j : Fin n) : ℕ :=
  ∑ offset : Fin W, (2 + FixedWordRegion.accessWork primitive (FixedWordRegion.localAddress j offset).val)

theorem fetchWork_bound {n W : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (j : Fin n) :
    fetchWork (W := W) primitive j ≤ W * (2 + FixedWordRegion.accessBound c 0 n W) := by
  calc
    _ ≤ ∑ _offset : Fin W, (2 + FixedWordRegion.accessBound c 0 n W) := Finset.sum_le_sum (fun offset _ =>
      Nat.add_le_add_left (by simpa only [Nat.zero_add] using
        FixedWordRegion.accessWork_bound primitive c hPrimitive 0 (FixedWordRegion.localAddress j offset)) 2)
    _ = _ := by simp

def readingWork {n W : ℕ} (model : RationalCostModel) (primitive : ℕ → ℕ) (m : ℕ)
    (memory : Fin (n * W) → Bool) (j : Fin n) : ℕ :=
  let frame := List.ofFn (fun offset => memory (FixedWordRegion.localAddress j offset))
  fetchWork (W := W) primitive j + BinaryPayload.bufferCopyWork W 0 + indexedLoopMetadataBitWork primitive 0 W +
    BinaryRouteFrame.decodingWork model primitive m frame + BinaryRouteFrame.decoderMetadataWork primitive m frame

def readingBound (model : RationalCostModel) (c n m W : ℕ) : ℕ :=
  W * (2 + FixedWordRegion.accessBound c 0 n W) + W * (W + 1) + indexedLoopMetadataBound c W +
    BinaryRouteFrame.decodingBound model c m W + 3 * BinaryRouteFrame.naturalMetadataBound c W

theorem readingWork_bound {n W : ℕ} (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (m : ℕ) (memory : Fin (n * W) → Bool) (j : Fin n) :
    readingWork model primitive m memory j ≤ readingBound model c n m W := by
  let frame := List.ofFn (fun offset : Fin W => memory (FixedWordRegion.localAddress j offset))
  have hFetch := fetchWork_bound (W := W) primitive c hPrimitive j
  have hLoop := indexedLoopMetadataBitWork_bound primitive c hPrimitive W
  have hDecode : BinaryRouteFrame.decodingWork model primitive m frame ≤ BinaryRouteFrame.decodingBound model c m W := by
    simpa only [frame, List.length_ofFn] using BinaryRouteFrame.decodingWork_bound model primitive c hPrimitive m frame
  have hMeta : BinaryRouteFrame.decoderMetadataWork primitive m frame ≤ 3 * BinaryRouteFrame.naturalMetadataBound c W := by
    simpa only [frame, List.length_ofFn] using BinaryRouteFrame.decoderMetadataWork_bound primitive c hPrimitive m frame
  dsimp only [frame] at hDecode hMeta
  unfold readingWork readingBound
  dsimp only
  rw [BinaryPayload.bufferCopyWork_eq]
  simp only [Nat.mul_zero, Nat.zero_add]
  omega

end Blotto.BinaryRouteSlot

namespace Blotto.RationalTerminalPacking
open scoped BigOperators

def emissionRouteReadingWork {n : ℕ} {i : RationalTerminalLotto n} (_p : RationalTerminalPacking i) {W : ℕ}
    (model : RationalCostModel) (primitive : ℕ → ℕ) (memory : Fin (n * W) → Bool) : ℕ :=
  ∑ j : Fin n, BinaryRouteSlot.readingWork model primitive i.groups.length memory j

theorem emissionRouteReadingWork_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) {W : ℕ}
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (memory : Fin (n * W) → Bool) :
    p.emissionRouteReadingWork model primitive memory ≤ n * BinaryRouteSlot.readingBound model c n i.groups.length W := by
  calc
    _ ≤ ∑ _j : Fin n, BinaryRouteSlot.readingBound model c n i.groups.length W := Finset.sum_le_sum (fun j _ =>
      BinaryRouteSlot.readingWork_bound model primitive c hPrimitive i.groups.length memory j)
    _ = _ := by simp

end Blotto.RationalTerminalPacking
