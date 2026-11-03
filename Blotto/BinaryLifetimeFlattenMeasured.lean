import Blotto.BinaryLifetimeFlattenList

/-! The list-only flatten loop returns its actual concatenation and a
source charge together. The copied-cell count and outer control are explicit;
native trace-observer arithmetic and reference-bit transport remain separate. -/
namespace Blotto.BinaryLifetimeFlattenMeasured
open BinaryLifetimeFlattenList
set_option autoImplicit false

def reversePush {α : Type*} : List α → List α → List α × ℕ
  | [],acc => (acc,2)
  | item::rest,acc =>
      let later := reversePush rest (item::acc)
      (later.1,later.2+4)

theorem reversePush_data {α : Type*} (items acc : List α) :
    (reversePush items acc).1 = BinaryLifetimeFlattenList.reversePush items acc := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih => simp only [reversePush,BinaryLifetimeFlattenList.reversePush,ih]

theorem reversePush_work {α : Type*} (items acc : List α) : (reversePush items acc).2 = 4*items.length+2 := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih => simp only [reversePush,List.length_cons,ih]; omega

def gather {α : Type*} : List (List α) → List α → List α × ℕ
  | [],acc => reversePush acc []
  | child::rest,acc =>
      let first := reversePush child acc
      let later := gather rest first.1
      (later.1,first.2+later.2+4)

theorem gather_data {α : Type*} (lists : List (List α)) (acc : List α) :
    (gather lists acc).1 = BinaryLifetimeFlattenList.gather lists acc := by
  induction lists generalizing acc with
  | nil => exact reversePush_data acc []
  | cons child rest ih => simp only [gather,BinaryLifetimeFlattenList.gather,reversePush_data,ih]

theorem gather_work {α : Type*} (lists : List (List α)) (acc : List α) :
    (gather lists acc).2 = 8*payloadCount lists+6*lists.length+4*acc.length+2 := by
  induction lists generalizing acc with
  | nil => simp [gather,reversePush_work,payloadCount]
  | cons child rest ih =>
      simp only [gather,reversePush_work,ih,reversePush_data,BinaryLifetimeFlattenList.reversePush_length,
        payloadCount,List.map_cons,List.sum_cons,List.length_cons]
      omega

def flatten {α : Type*} (lists : List (List α)) : List α × ℕ := gather lists []

theorem flatten_data {α : Type*} (lists : List (List α)) :
    (flatten lists).1 = BinaryLifetimeFlattenList.flattenDirect lists := gather_data lists []

theorem flatten_work {α : Type*} (lists : List (List α)) :
    (flatten lists).2 = 8*payloadCount lists+6*lists.length+2 := by
  simpa only [flatten,List.length_nil,mul_zero,Nat.add_zero] using gather_work lists []

end Blotto.BinaryLifetimeFlattenMeasured
