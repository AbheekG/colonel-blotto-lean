import Blotto.BinaryAddressFormation
import Blotto.BinaryFrameEncodingMetadata

/-! Forming one address includes four operand bit extractions, their buffer
and iterator work, then Boolean multiplication/addition. Actual operand widths
are bounded from the allocated region; primitive monotonicity is not assumed.
Concrete machine/allocator interpretation remains separate. -/

namespace Blotto.BinaryAddressFormation

def operandWork (primitive : ℕ → ℕ) (S value : ℕ) : ℕ :=
  BinaryPayload.encodingBitWork primitive S value + BinaryPayload.bufferCopyWork S 0 + indexedLoopMetadataBitWork primitive 0 S

def operandBound (c S : ℕ) : ℕ :=
  S * ((1 + c) * (2 * S) + 1) + S * (S + 1) + indexedLoopMetadataBound c S

theorem operandWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (S value : ℕ) (hWidth : binaryWordWidth value ≤ S) : operandWork primitive S value ≤ operandBound c S := by
  have hp := (BinaryPayload.encodingBitWork_bound primitive c hPrimitive S value).trans
    (Nat.mul_le_mul_left S (Nat.add_le_add_right
      (Nat.mul_le_mul_left (1 + c) (show binaryWordWidth value + S ≤ 2 * S by omega)) 1))
  have hLoop := indexedLoopMetadataBitWork_bound primitive c hPrimitive S
  unfold operandWork operandBound
  rw [BinaryPayload.bufferCopyWork_eq]
  simp only [Nat.mul_zero, Nat.zero_add]
  omega

def encodedWork {n W : ℕ} (primitive : ℕ → ℕ) (base : ℕ) (j : Fin n) (offset : Fin W) : ℕ :=
  let S := FixedWordRegion.addressWidth base n W
  operandWork primitive S base + operandWork primitive S j.val + operandWork primitive S W + operandWork primitive S offset.val +
    work (BinaryPayload.bits S base) (BinaryPayload.bits S j.val) (BinaryPayload.bits S W) (BinaryPayload.bits S offset.val)

def encodedWorkBound (c base n W : ℕ) : ℕ :=
  4 * operandBound c (FixedWordRegion.addressWidth base n W) + workBound (FixedWordRegion.addressWidth base n W)

theorem encodedWork_bound {n W : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (base : ℕ) (j : Fin n) (offset : Fin W) : encodedWork primitive base j offset ≤ encodedWorkBound c base n W := by
  let S := FixedWordRegion.addressWidth base n W
  have hValues := address_operand_bounds base j offset
  have hBase := operandWork_bound primitive c hPrimitive S base (binaryWordWidth_mono hValues.1)
  have hIndex := operandWork_bound primitive c hPrimitive S j.val (binaryWordWidth_mono hValues.2.1)
  have hStride := operandWork_bound primitive c hPrimitive S W (binaryWordWidth_mono hValues.2.2.1)
  have hOffset := operandWork_bound primitive c hPrimitive S offset.val (binaryWordWidth_mono hValues.2.2.2)
  have hForm := work_bound (BinaryPayload.bits S base) (BinaryPayload.bits S j.val) (BinaryPayload.bits S W) (BinaryPayload.bits S offset.val)
    S (le_of_eq (BinaryPayload.bits_length _ _)) (le_of_eq (BinaryPayload.bits_length _ _))
      (le_of_eq (BinaryPayload.bits_length _ _)) (le_of_eq (BinaryPayload.bits_length _ _))
  change encodedWork primitive base j offset ≤ 4 * operandBound c S + workBound S
  unfold encodedWork
  dsimp only
  change operandWork primitive S base + operandWork primitive S j.val + operandWork primitive S W + operandWork primitive S offset.val +
    work (BinaryPayload.bits S base) (BinaryPayload.bits S j.val) (BinaryPayload.bits S W) (BinaryPayload.bits S offset.val) ≤ _
  omega

end Blotto.BinaryAddressFormation
