import Blotto.GeneralPaperEqualBooleanCategoricalContract
import Blotto.GeneralPaperNativeFreshBufferBits
import Blotto.BinaryPayloadMergeBitWork

/-! The balanced integer decoder computes each child once and returns its
actual merge/copy/index/control price. Arrays use the paper reference model;
natural shift/add and index operations have the declared linear bit price. -/
namespace Blotto.GeneralPaperBalancedBitDecoder
open BinaryPayload
set_option autoImplicit false
set_option maxHeartbeats 900000

structure Result where
  value : ℕ
  work : ℕ

def mergePrice (primitive : ℕ → ℕ) (low x y : ℕ) : ℕ :=
  let z := y <<< low
  binaryWordWidth x + binaryWordWidth y + binaryWordWidth z + binaryWordWidth (x + z) +
    primitive (binaryWordWidth y + low) + primitive (max (binaryWordWidth x) (binaryWordWidth z))

def nodePrice (primitive : ℕ → ℕ) (A : ℕ) (buffer : Array Bool) (pos length : ℕ) : ℕ :=
  let W := indexMetadataWordWidth buffer pos length
  12 * W + 6 * primitive W + 8 + 16 * A

def run (primitive : ℕ → ℕ) (A : ℕ) (buffer : Array Bool) (pos length : ℕ) : Result :=
  let node := nodePrice primitive A buffer pos length
  if length = 0 then ⟨0, node⟩ else if length = 1 then
    ⟨if buffer.getD pos false then 1 else 0, node + 1⟩
  else
    let low := length / 2
    let first := run primitive A buffer pos low
    let second := run primitive A buffer (pos + low) (length - low)
    let shifted := second.value <<< low
    ⟨first.value + shifted, first.work + second.work + mergePrice primitive low first.value second.value + node⟩
termination_by length
decreasing_by all_goals omega

theorem data (primitive : ℕ → ℕ) (A : ℕ) (buffer : Array Bool) (pos length : ℕ) :
    (run primitive A buffer pos length).value = balancedValue buffer pos length := by
  conv => lhs; rw [run]
  conv => rhs; rw [balancedValue]
  dsimp only
  split
  · rfl
  · split
    · rfl
    · rw [data primitive A buffer pos (length / 2), data primitive A buffer (pos + length / 2) (length - length / 2)]
termination_by length
decreasing_by all_goals omega

theorem work_eq (primitive : ℕ → ℕ) (A : ℕ) (buffer : Array Bool) (pos length : ℕ) :
    (run primitive A buffer pos length).work = balancedBitWork primitive buffer pos length +
      indexMetadataBitWork primitive buffer pos length + 16 * A * metadataNodeCount length := by
  conv => lhs; rw [run]
  dsimp only
  by_cases h0 : length = 0
  · subst length
    simp [balancedBitWork, indexMetadataBitWork, metadataNodeCount, nodePrice]
  · by_cases h1 : length = 1
    · subst length
      simp [balancedBitWork, indexMetadataBitWork, metadataNodeCount, nodePrice]
      omega
    · rw [ite_eq_right h0, ite_eq_right h1]
      dsimp only
      rw [work_eq primitive A buffer pos (length / 2),
        work_eq primitive A buffer (pos + length / 2) (length - length / 2), data, data]
      conv => rhs; rw [balancedBitWork, ite_eq_right h0, ite_eq_right h1,
        indexMetadataBitWork, ite_eq_right (by omega : ¬length ≤ 1),
        metadataNodeCount, ite_eq_right (by omega : ¬length ≤ 1)]
      unfold mergePrice mergeBitPrice nodePrice
      ring
termination_by length
decreasing_by all_goals omega

theorem work_bound (primitive : ℕ → ℕ) (c : ℕ) (hp : ∀ w, primitive w ≤ c * w)
    (A : ℕ) (buffer : Array Bool) (pos length : ℕ) :
    (run primitive A buffer pos length).work ≤ length + (4 + 2 * c) * length * binaryWordWidth length +
      (2 * length + 1) * ((12 + 6 * c) * indexMetadataWordWidth buffer pos length + 8 + 16 * A) := by
  rw [work_eq]
  have h1 := balancedBitWork_word_bound primitive c hp buffer pos length
  have h2 := indexMetadataBitWork_bound primitive c hp buffer pos length
  have h3 : metadataNodeCount length ≤ 2 * length + 1 := by rw [metadataNodeCount_eq]; split <;> omega
  have h4 := Nat.mul_le_mul_left (16 * A) h3
  nlinarith only [h1, h2, h4]

end Blotto.GeneralPaperBalancedBitDecoder
