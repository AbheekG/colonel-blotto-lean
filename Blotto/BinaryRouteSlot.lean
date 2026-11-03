import Blotto.BinaryRouteFrame
import Blotto.FixedBinaryWordAccess
import Blotto.FixedWordStoreRAM

/-! Bounded route frames fit fixed-width bit slots with deterministic padding.
Readback is exact, including the rational coefficient. Oversized frames are
reported by an explicit fit requirement; no encoded field is truncated. -/

namespace Blotto.BinaryRouteSlot

def encode {m : ℕ} (W : ℕ) (route : GroupRoute m) (hFit : (BinaryRouteFrame.encode route).length ≤ W) : FixedBinaryWord W :=
  FixedBinaryWord.pad W (BinaryRouteFrame.encode route) hFit

def read {W : ℕ} (m : ℕ) (word : Fin W → Bool) : Option (GroupRoute m) :=
  (BinaryRouteFrame.read m (List.ofFn word)).map Prod.fst

theorem read_encode {m : ℕ} (W : ℕ) (route : GroupRoute m) (hFit : (BinaryRouteFrame.encode route).length ≤ W) :
    read m (encode W route hFit).bit = some route := by
  unfold read encode
  rw [FixedBinaryWord.pad_readback, BinaryRouteFrame.read_encode_append]
  rfl

theorem frame_fit_of_payload {m : ℕ} (route : GroupRoute m) (P : ℕ) (h : routePayloadWordWidth route ≤ P) :
    (BinaryRouteFrame.encode route).length ≤ 2 * P + 1 :=
  (BinaryRouteFrame.encode_length_bound route).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 1)

theorem stored_readback {n m W : ℕ} {β : Type*} (j : Fin n) (route : GroupRoute m)
    (hFit : (BinaryRouteFrame.encode route).length ≤ W) (memory : Fin (n * W) → Bool) (frame : β) :
    read m (fun offset => (FixedWordStoreRAM.store j (encode W route hFit).bit memory frame).cells
      (FixedWordRegion.localAddress j offset)) = some route := by
  have hWord : (fun offset => (FixedWordStoreRAM.store j (encode W route hFit).bit memory frame).cells
      (FixedWordRegion.localAddress j offset)) = (encode W route hFit).bit := by
    funext offset
    rw [FixedWordStoreRAM.store_read]
    simp only [ite_true]
  rw [hWord]
  exact read_encode W route hFit

theorem stored_other_slot {n m W : ℕ} {β : Type*} (j k : Fin n) (hjk : k ≠ j) (route : GroupRoute m)
    (hFit : (BinaryRouteFrame.encode route).length ≤ W) (memory : Fin (n * W) → Bool) (frame : β) :
    read m (fun offset => (FixedWordStoreRAM.store j (encode W route hFit).bit memory frame).cells
      (FixedWordRegion.localAddress k offset)) = read m (fun offset => memory (FixedWordRegion.localAddress k offset)) := by
  congr 1
  funext offset
  rw [FixedWordStoreRAM.store_read, ite_eq_right hjk]

end Blotto.BinaryRouteSlot
