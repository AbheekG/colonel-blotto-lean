import Blotto.BinarySeedPreparationSpace

/-! A list-only, tail-recursive flatten backend for trace children. It
traverses each child into a reversed accumulator, then reverses once. The
observer is separate from the selected value program; its cons count is
exactly twice the payload length. -/
namespace Blotto.BinaryLifetimeFlattenList
set_option autoImplicit false

def reversePush {α : Type*} : List α → List α → List α
  | [], acc => acc
  | item :: rest, acc => reversePush rest (item :: acc)

theorem reversePush_result {α : Type*} (items acc : List α) :
    reversePush items acc = items.reverse ++ acc := by
  induction items generalizing acc with
  | nil => simp [reversePush]
  | cons item rest ih =>
      simp only [reversePush,ih,List.reverse_cons,List.singleton_append,
        List.append_assoc]

theorem reversePush_length {α : Type*} (items acc : List α) :
    (reversePush items acc).length = items.length + acc.length := by
  rw [reversePush_result]
  simp

def gather {α : Type*} : List (List α) → List α → List α
  | [], acc => reversePush acc []
  | child :: rest, acc => gather rest (reversePush child acc)

theorem gather_result {α : Type*} (lists : List (List α)) (acc : List α) :
    gather lists acc = acc.reverse ++ lists.flatten := by
  induction lists generalizing acc with
  | nil => simp [gather,reversePush_result]
  | cons child rest ih =>
      simp only [gather,ih,reversePush_result,List.reverse_append,
        List.reverse_reverse,List.flatten_cons]
      simp only [List.append_assoc]

def flattenDirect {α : Type*} (lists : List (List α)) : List α :=
  gather lists []

theorem flattenDirect_result {α : Type*} (lists : List (List α)) :
    flattenDirect lists = lists.flatten := by
  simpa [flattenDirect] using gather_result lists []

theorem flattenDirect_eq_flattenTR {α : Type*} (lists : List (List α)) :
    flattenDirect lists = List.flattenTR lists := by
  rw [flattenDirect_result,← List.flatten_eq_flattenTR]

def reversePushWithCount {α : Type*} : List α → List α → List α × ℕ
  | [], acc => (acc,0)
  | item :: rest, acc =>
      let later := reversePushWithCount rest (item :: acc)
      (later.1,later.2+1)

theorem reversePushWithCount_state {α : Type*} (items acc : List α) :
    (reversePushWithCount items acc).1 = reversePush items acc := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih =>
      simp only [reversePushWithCount,reversePush,ih]

theorem reversePushWithCount_count {α : Type*} (items acc : List α) :
    (reversePushWithCount items acc).2 = items.length := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih =>
      simp only [reversePushWithCount,List.length_cons,ih]

def payloadCount {α : Type*} (lists : List (List α)) : ℕ :=
  (lists.map List.length).sum

def gatherWithCount {α : Type*} : List (List α) → List α → List α × ℕ
  | [], acc => reversePushWithCount acc []
  | child :: rest, acc =>
      let first := reversePushWithCount child acc
      let later := gatherWithCount rest first.1
      (later.1,first.2+later.2)

theorem gatherWithCount_state {α : Type*} (lists : List (List α)) (acc : List α) :
    (gatherWithCount lists acc).1 = gather lists acc := by
  induction lists generalizing acc with
  | nil => exact reversePushWithCount_state acc []
  | cons child rest ih =>
      simp only [gatherWithCount,gather,reversePushWithCount_state,ih]

theorem gatherWithCount_count {α : Type*} (lists : List (List α)) (acc : List α) :
    (gatherWithCount lists acc).2 = 2*payloadCount lists + acc.length := by
  induction lists generalizing acc with
  | nil => simp [gatherWithCount,reversePushWithCount_count,payloadCount]
  | cons child rest ih =>
      have hLength := reversePush_length child acc
      simp only [gatherWithCount,reversePushWithCount_count,
        reversePushWithCount_state,ih,payloadCount,List.map_cons,List.sum_cons]
      omega

theorem flattenDirect_cons_count {α : Type*} (lists : List (List α)) :
    (gatherWithCount lists []).1 = flattenDirect lists ∧
    (gatherWithCount lists []).2 = 2*payloadCount lists := by
  exact ⟨gatherWithCount_state lists [],by simpa using gatherWithCount_count lists []⟩

end Blotto.BinaryLifetimeFlattenList
