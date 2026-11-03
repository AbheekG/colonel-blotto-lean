module
import all Init.Data.Array.Basic
public import Blotto.NativeArrayCoreControl
public import Init.Data.Array.Bootstrap
public section
universe u

/-! Exact source control for list-to-array pushes and the pinned safe foldr
reference underlying Array.toListImpl. Observations track actual array sizes,
descending read indices and reference counts. This is not a theorem about the
host's USize specialization, allocator capacities or physical reference bits. -/
namespace Blotto.NativeArrayConversionCore

structure PushSnapshot where
  remaining : Nat
  used : Nat
  deriving Repr, DecidableEq

def PushSnapshot.Valid (capacity : Nat) (s : PushSnapshot) : Prop := s.used+s.remaining = capacity

def PushSnapshot.operands (capacity : Nat) (s : PushSnapshot) : List Nat := [capacity,s.used,s.used+1]

theorem PushSnapshot.operand_bound {capacity : Nat} {s : PushSnapshot} (h : s.Valid capacity) :
    ∀ value ∈ s.operands capacity,value ≤ capacity+1 := by
  intro value hv
  simp only [PushSnapshot.operands,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl <;> unfold PushSnapshot.Valid at h <;> omega

def pushLoop {α : Type u} : List α → Array α → Array α × List PushSnapshot
  | [], acc => (acc,[⟨0,acc.size⟩])
  | item::rest, acc =>
      let next := pushLoop rest (acc.push item)
      (next.1,⟨rest.length+1,acc.size⟩::next.2)

theorem pushLoop_state {α : Type u} (items : List α) (acc : Array α) :
    (pushLoop items acc).1 = List.toArrayAux items acc := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih => exact ih (acc.push item)

theorem pushLoop_length {α : Type u} (items : List α) (acc : Array α) :
    (pushLoop items acc).2.length = items.length+1 := by
  induction items generalizing acc with
  | nil => rfl
  | cons item rest ih => simp only [pushLoop,List.length_cons,ih]

theorem pushLoop_valid {α : Type u} (items : List α) (acc : Array α) (capacity : Nat)
    (h : acc.size+items.length = capacity) : ∀ s ∈ (pushLoop items acc).2,s.Valid capacity := by
  induction items generalizing acc with
  | nil =>
      intro s hs
      simp only [pushLoop,List.mem_singleton] at hs
      subst s
      exact h
  | cons item rest ih =>
      intro s hs
      simp only [pushLoop,List.mem_cons] at hs
      rcases hs with hs|hs
      · subst s
        exact h
      · exact ih (acc.push item) (by simp only [Array.size_push,List.length_cons] at *; omega) s hs

def pack {α : Type u} (items : List α) : Array α × List PushSnapshot :=
  pushLoop items (Array.emptyWithCapacity items.length)

theorem pack_state {α : Type u} (items : List α) : (pack items).1 = items.toArray := by
  apply Array.toList_inj.mp
  simp [pack,pushLoop_state,Array.toArrayAux_eq]

theorem pack_length {α : Type u} (items : List α) : (pack items).2.length = items.length+1 :=
  pushLoop_length items _

theorem pack_valid {α : Type u} (items : List α) : ∀ s ∈ (pack items).2,s.Valid items.length :=
  pushLoop_valid items _ items.length (by simp)

structure ReadSnapshot where
  remaining : Nat
  index : Nat
  accumulated : Nat
  deriving Repr, DecidableEq

def ReadSnapshot.Valid (size : Nat) (s : ReadSnapshot) : Prop :=
  s.remaining ≤ size ∧ s.index = s.remaining-1 ∧ s.accumulated+s.remaining = size

def ReadSnapshot.operands (size : Nat) (s : ReadSnapshot) : List Nat := [size,s.remaining,s.remaining-1,s.index,0]

theorem ReadSnapshot.operand_bound {size : Nat} {s : ReadSnapshot} (h : s.Valid size) :
    ∀ value ∈ s.operands size,value ≤ size+1 := by
  intro value hv
  simp only [ReadSnapshot.operands,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl <;> unfold ReadSnapshot.Valid at h <;> omega

def readLoop {α : Type u} (data : Array α) (acc : List α) :
    (remaining : Nat) → remaining ≤ data.size → List α × List ReadSnapshot
  | 0, _ => (acc,[⟨0,0,acc.length⟩])
  | remaining+1, h =>
      let next := readLoop data (data[remaining]'(by omega)::acc) remaining (by omega)
      (next.1,⟨remaining+1,remaining,acc.length⟩::next.2)

def coreReadLoop {α : Type u} (data : Array α) (acc : List α) (remaining : Nat) (h : remaining ≤ data.size) : List α :=
  Array.foldrM.fold (m := Id) (fun value rest => pure (value::rest)) data 0 remaining h acc

theorem readLoop_state {α : Type u} (data : Array α) (acc : List α) (remaining : Nat) (h : remaining ≤ data.size) :
    (readLoop data acc remaining h).1 = coreReadLoop data acc remaining h := by
  induction remaining generalizing acc with
  | zero => rfl
  | succ remaining ih =>
      have hNext := ih (data[remaining]'(by omega)::acc) (by omega)
      simpa [readLoop,coreReadLoop,Array.foldrM.fold,Id.run] using hNext

theorem readLoop_length {α : Type u} (data : Array α) (acc : List α) (remaining : Nat) (h : remaining ≤ data.size) :
    (readLoop data acc remaining h).2.length = remaining+1 := by
  induction remaining generalizing acc with
  | zero => rfl
  | succ remaining ih => simp only [readLoop,List.length_cons,ih]

theorem readLoop_valid {α : Type u} (data : Array α) (acc : List α) (remaining : Nat) (h : remaining ≤ data.size)
    (hSize : acc.length+remaining = data.size) : ∀ s ∈ (readLoop data acc remaining h).2,s.Valid data.size := by
  induction remaining generalizing acc with
  | zero =>
      intro s hs
      simp only [readLoop,List.mem_singleton] at hs
      subst s
      exact ⟨Nat.zero_le _,rfl,hSize⟩
  | succ remaining ih =>
      intro s hs
      simp only [readLoop,List.mem_cons] at hs
      rcases hs with hs|hs
      · subst s
        exact ⟨h,by simp,hSize⟩
      · exact ih (data[remaining]'(by omega)::acc) (by omega) (by simp only [List.length_cons]; omega) s hs

def read {α : Type u} (data : Array α) : List α × List ReadSnapshot := readLoop data [] data.size (Nat.le_refl _)

theorem read_state_impl {α : Type u} (data : Array α) : (read data).1 = data.toListImpl := by
  by_cases hPos : 0 < data.size
  · have h := readLoop_state data [] data.size (Nat.le_refl _)
    simpa [read,Array.toListImpl,Array.foldr,Array.foldrM,coreReadLoop,hPos,Id.run] using h
  · have hz : data.size = 0 := by omega
    simp [read,readLoop,Array.toListImpl,Array.foldr,Array.foldrM,hz]

theorem read_state {α : Type u} (data : Array α) : (read data).1 = data.toList := by
  rw [read_state_impl,Array.toListImpl_eq]

theorem read_length {α : Type u} (data : Array α) : (read data).2.length = data.size+1 :=
  readLoop_length data [] _ _

theorem read_valid {α : Type u} (data : Array α) : ∀ s ∈ (read data).2,s.Valid data.size :=
  readLoop_valid data [] _ _ (by simp)

def ReadSnapshot.readIndex (s : ReadSnapshot) : Option Nat :=
  match s.remaining with
  | 0 => none
  | _+1 => some s.index

theorem readLoop_indices {α : Type u} (data : Array α) (acc : List α) (remaining : Nat) (h : remaining ≤ data.size) :
    (readLoop data acc remaining h).2.filterMap ReadSnapshot.readIndex = (List.range remaining).reverse := by
  induction remaining generalizing acc with
  | zero => simp [readLoop,ReadSnapshot.readIndex]
  | succ remaining ih => simp only [readLoop,List.filterMap_cons,ReadSnapshot.readIndex,ih,List.range_succ,
      List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append]

theorem read_indices {α : Type u} (data : Array α) :
    (read data).2.filterMap ReadSnapshot.readIndex = (List.range data.size).reverse := readLoop_indices data [] _ _

end Blotto.NativeArrayConversionCore
