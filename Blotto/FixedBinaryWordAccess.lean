import Blotto.FixedBinaryWord

/-! Width-indexed word access and padding retain an entire framed prefix.
The fit proof prevents truncation. Padding is deterministic and readback
recovers the exact stored list. -/

namespace Blotto.FixedBinaryWord

def bit {W : ℕ} (word : FixedBinaryWord W) (offset : Fin W) : Bool :=
  word.bits[offset.val]'(by rw [word.size]; exact offset.isLt)

theorem ofFn_bit {W : ℕ} (word : FixedBinaryWord W) : List.ofFn word.bit = word.bits := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, word.size]
  · intro index hLeft hRight
    rw [List.getElem_ofFn]
    rfl

def pad (W : ℕ) (frame : List Bool) (hFit : frame.length ≤ W) : FixedBinaryWord W :=
  ⟨frame ++ List.replicate (W - frame.length) false, by simp only [List.length_append, List.length_replicate]; omega⟩

theorem pad_bits (W : ℕ) (frame : List Bool) (hFit : frame.length ≤ W) :
    (pad W frame hFit).bits = frame ++ List.replicate (W - frame.length) false := rfl

theorem pad_readback (W : ℕ) (frame : List Bool) (hFit : frame.length ≤ W) :
    List.ofFn (pad W frame hFit).bit = frame ++ List.replicate (W - frame.length) false := by
  rw [ofFn_bit, pad_bits]

end Blotto.FixedBinaryWord
