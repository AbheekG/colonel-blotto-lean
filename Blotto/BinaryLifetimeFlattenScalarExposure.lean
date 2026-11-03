import Blotto.BinaryLifetimeFlattenControl

/-! Bit-width exposure of the scalar operands in the retained array-based
`List.flattenTR` reference path. The selected `fromEntries` path now uses
`BinaryLifetimeFlattenList.flattenDirect`. This observer remains a checked
comparison, not a price for the selected list backend. -/
namespace Blotto.BinaryLifetimeFlattenScalarExposure
open NativeArrayConversionCore NativeArrayConversionControl
open BinaryLifetimeFlattenControl
set_option autoImplicit false

def pushSnapshotBits (capacity : ℕ) (s : PushSnapshot) : ℕ :=
  (s.operands capacity |>.map binaryWordWidth).sum

def readSnapshotBits (size : ℕ) (s : ReadSnapshot) : ℕ :=
  (s.operands size |>.map binaryWordWidth).sum

def pushBits (capacity : ℕ) (snapshots : List PushSnapshot) : ℕ :=
  (snapshots.map (pushSnapshotBits capacity)).sum

def readBits (size : ℕ) (snapshots : List ReadSnapshot) : ℕ :=
  (snapshots.map (readSnapshotBits size)).sum

theorem pushSnapshotBits_bound {capacity : ℕ} {s : PushSnapshot}
    (h : s.Valid capacity) :
    pushSnapshotBits capacity s ≤ 3*binaryWordWidth (capacity+1) := by
  have hUsed : s.used ≤ capacity+1 := by
    unfold PushSnapshot.Valid at h
    omega
  have hNext : s.used+1 ≤ capacity+1 := by
    unfold PushSnapshot.Valid at h
    omega
  have h1 := binaryWordWidth_mono (show capacity ≤ capacity+1 by omega)
  have h2 := binaryWordWidth_mono hUsed
  have h3 := binaryWordWidth_mono hNext
  simp only [pushSnapshotBits,PushSnapshot.operands,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil]
  omega

theorem readSnapshotBits_bound {size : ℕ} {s : ReadSnapshot}
    (h : s.Valid size) :
    readSnapshotBits size s ≤ 5*binaryWordWidth (size+1) := by
  have hBound := ReadSnapshot.operand_bound h
  have h1 := binaryWordWidth_mono (hBound size (by simp [ReadSnapshot.operands]))
  have h2 := binaryWordWidth_mono (hBound s.remaining (by simp [ReadSnapshot.operands]))
  have h3 := binaryWordWidth_mono (hBound (s.remaining-1) (by simp [ReadSnapshot.operands]))
  have h4 := binaryWordWidth_mono (hBound s.index (by simp [ReadSnapshot.operands]))
  have h5 := binaryWordWidth_mono (hBound 0 (by simp [ReadSnapshot.operands]))
  simp only [readSnapshotBits,ReadSnapshot.operands,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil]
  omega

theorem pushBits_bound (capacity : ℕ) (snapshots : List PushSnapshot)
    (h : ∀ s ∈ snapshots, s.Valid capacity) :
    pushBits capacity snapshots ≤ snapshots.length *
      (3*binaryWordWidth (capacity+1)) := by
  induction snapshots with
  | nil => simp [pushBits]
  | cons s rest ih =>
      have hs := pushSnapshotBits_bound (h s (by simp))
      have hr := ih (fun t ht => h t (by simp [ht]))
      simp only [pushBits,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul] at *
      omega

theorem readBits_bound (size : ℕ) (snapshots : List ReadSnapshot)
    (h : ∀ s ∈ snapshots, s.Valid size) :
    readBits size snapshots ≤ snapshots.length *
      (5*binaryWordWidth (size+1)) := by
  induction snapshots with
  | nil => simp [readBits]
  | cons s rest ih =>
      have hs := readSnapshotBits_bound (h s (by simp))
      have hr := ih (fun t ht => h t (by simp [ht]))
      simp only [readBits,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul] at *
      omega

def selectedBits {α : Type*} (lists : List (List α)) : ℕ :=
  let T := payloadCount lists
  pushBits T (pushLoop lists.flatten #[]).2 +
    readBits (flattenWithCount lists #[]).1.size
      (read (flattenWithCount lists #[]).1).2

theorem selectedBits_bound {α : Type*} (lists : List (List α)) :
    selectedBits lists ≤
      8*(payloadCount lists+1)*binaryWordWidth (payloadCount lists+1) := by
  let T := payloadCount lists
  have hLength : lists.flatten.length = T := by simp [T,payloadCount]
  have hValid := pushLoop_valid lists.flatten (#[] : Array α) T (by simp [hLength])
  have hPush := pushBits_bound T (pushLoop lists.flatten (#[] : Array α)).2 hValid
  rw [pushLoop_length,hLength] at hPush
  have hSize : (flattenWithCount lists #[]).1.size = T := by
    rw [← Array.length_toList,(selected_flatten_count lists).1]
    simp [T,payloadCount,← List.flatten_eq_flattenTR]
  have hRead := readBits_bound (flattenWithCount lists #[]).1.size
    (read (flattenWithCount lists #[]).1).2 (read_valid _)
  rw [read_length,hSize] at hRead
  unfold selectedBits
  dsimp only
  rw [hSize]
  nlinarith only [hPush,hRead]

theorem pairBits_bound {α β : Type*} (first : List (List α))
    (second : List (List β)) (B : ℕ)
    (h : payloadCount first + payloadCount second ≤ B) :
    selectedBits first + selectedBits second ≤
      8*(B+2)*binaryWordWidth (B+1) := by
  let W := binaryWordWidth (B+1)
  have hW1 : binaryWordWidth (payloadCount first+1) ≤ W :=
    binaryWordWidth_mono (by omega)
  have hW2 : binaryWordWidth (payloadCount second+1) ≤ W :=
    binaryWordWidth_mono (by omega)
  have hFirst : selectedBits first ≤ 8*(payloadCount first+1)*W :=
    (selectedBits_bound first).trans (Nat.mul_le_mul_left _ hW1)
  have hSecond : selectedBits second ≤ 8*(payloadCount second+1)*W :=
    (selectedBits_bound second).trans (Nat.mul_le_mul_left _ hW2)
  calc
    _ ≤ 8*(payloadCount first+1)*W + 8*(payloadCount second+1)*W :=
      Nat.add_le_add hFirst hSecond
    _ = 8*(payloadCount first+payloadCount second+2)*W := by ring
    _ ≤ 8*(B+2)*W :=
      Nat.mul_le_mul_right W (Nat.mul_le_mul_left 8 (by omega))

end Blotto.BinaryLifetimeFlattenScalarExposure
