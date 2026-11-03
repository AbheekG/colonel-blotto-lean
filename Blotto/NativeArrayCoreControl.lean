module
import all Init.Data.Array.Basic
public import Init.Data.Array.OfFn
public import Init.Data.List.Range
public import Init.Omega
public section
universe u

/-! The exact pinned Array.ofFn loop, with proof-only snapshots of its live
natural operands. This follows the native descending fuel and n-i-1 callback
index, rather than substituting a different iteration order. Every callback
occurs once. The internally derived scalar width does not price payloads,
reference transport, host allocation or the observation list. -/
namespace Blotto.NativeArrayCoreControl
set_option maxHeartbeats 2000000

structure Snapshot where
  remaining : Nat
  index : Nat
  used : Nat
  deriving Repr, DecidableEq

def Snapshot.Valid (limit : Nat) (s : Snapshot) : Prop :=
  s.remaining ≤ limit ∧ s.used+s.remaining = limit ∧ s.index = limit-s.remaining

def Snapshot.operands (limit : Nat) (s : Snapshot) : List Nat :=
  [limit,s.remaining,s.remaining+1,limit-(s.remaining-1),limit-(s.remaining-1)-1,s.index,s.used,s.used+1,limit+1]

theorem Snapshot.operand_bound {limit : Nat} {s : Snapshot} (h : s.Valid limit) :
    ∀ value ∈ s.operands limit,value ≤ limit+1 := by
  intro value hv
  simp only [Snapshot.operands,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Snapshot.Valid at h <;> omega

def loop {n : Nat} {α : Type u} (produce : Fin n → α) (acc : Array α) :
    (remaining : Nat) → remaining ≤ n → Array α × List Snapshot
  | 0, _ => (acc,[⟨0,n,acc.size⟩])
  | remaining+1, h =>
      let index : Fin n := ⟨n-remaining-1,by omega⟩
      let next := loop produce (acc.push (produce index)) remaining (by omega)
      (next.1,⟨remaining+1,index.val,acc.size⟩::next.2)

def coreLoop {n : Nat} {α : Type u} (produce : Fin n → α) (acc : Array α) (remaining : Nat) (h : remaining ≤ n) : Array α :=
  Array.ofFn.go produce acc remaining h

theorem loop_state {n : Nat} {α : Type u} (produce : Fin n → α) (acc : Array α) (remaining : Nat) (h : remaining ≤ n) :
    (loop produce acc remaining h).1 = coreLoop produce acc remaining h := by
  induction remaining generalizing acc with
  | zero => rfl
  | succ remaining ih => simpa only [loop,coreLoop,Array.ofFn.go] using ih (acc.push (produce ⟨n-remaining-1,by omega⟩)) (by omega)

theorem loop_length {n : Nat} {α : Type u} (produce : Fin n → α) (acc : Array α) (remaining : Nat) (h : remaining ≤ n) :
    (loop produce acc remaining h).2.length = remaining+1 := by
  induction remaining generalizing acc with
  | zero => rfl
  | succ remaining ih => simp only [loop,List.length_cons,ih]

theorem loop_valid {n : Nat} {α : Type u} (produce : Fin n → α) (acc : Array α) (remaining : Nat) (h : remaining ≤ n)
    (hSize : acc.size+remaining = n) : ∀ s ∈ (loop produce acc remaining h).2,s.Valid n := by
  induction remaining generalizing acc with
  | zero =>
      intro s hs
      simp only [loop,List.mem_singleton] at hs
      subst s
      change 0 ≤ n ∧ acc.size+0 = n ∧ n = n-0
      exact ⟨Nat.zero_le _,by omega,by omega⟩
  | succ remaining ih =>
      intro s hs
      simp only [loop,List.mem_cons] at hs
      rcases hs with hs|hs
      · subst s
        refine ⟨h,hSize,?_⟩
        change n-remaining-1 = n-(remaining+1)
        omega
      · exact ih (acc.push (produce ⟨n-remaining-1,by omega⟩)) (by omega) (by simp only [Array.size_push]; omega) s hs

def Snapshot.callback (s : Snapshot) : Option Nat :=
  match s.remaining with
  | 0 => none
  | _+1 => some s.index

theorem loop_callbacks {n : Nat} {α : Type u} (produce : Fin n → α) (acc : Array α) (remaining : Nat) (h : remaining ≤ n) :
    (loop produce acc remaining h).2.filterMap Snapshot.callback = List.range' (n-remaining) remaining := by
  induction remaining generalizing acc with
  | zero => simp [loop,Snapshot.callback]
  | succ remaining ih =>
      simp only [loop,List.filterMap_cons,Snapshot.callback,ih,List.range'_succ]
      rw [show n-remaining-1 = n-(remaining+1) by omega,
        show n-remaining = n-(remaining+1)+1 by omega]

def build {n : Nat} {α : Type u} (produce : Fin n → α) : Array α × List Snapshot :=
  loop produce (Array.emptyWithCapacity n) n (Nat.le_refl n)

theorem build_state {n : Nat} {α : Type u} (produce : Fin n → α) : (build produce).1 = Array.ofFn produce :=
  loop_state produce _ n (Nat.le_refl n)

theorem build_length {n : Nat} {α : Type u} (produce : Fin n → α) : (build produce).2.length = n+1 :=
  loop_length produce _ n (Nat.le_refl n)

theorem build_valid {n : Nat} {α : Type u} (produce : Fin n → α) : ∀ s ∈ (build produce).2,s.Valid n :=
  loop_valid produce _ n (Nat.le_refl n) (by simp)

theorem build_callbacks {n : Nat} {α : Type u} (produce : Fin n → α) :
    (build produce).2.filterMap Snapshot.callback = List.range n := by
  simpa only [build,Nat.sub_self,List.range_eq_range'] using loop_callbacks produce (Array.emptyWithCapacity n) n (Nat.le_refl n)


def copiedSlots (snapshots : List Snapshot) : Nat := (snapshots.map (fun s => s.used+1)).sum

theorem copiedSlots_bound (limit : Nat) (snapshots : List Snapshot) (h : ∀ s ∈ snapshots,s.Valid limit) :
    copiedSlots snapshots ≤ snapshots.length*(limit+1) := by
  induction snapshots with
  | nil => simp [copiedSlots]
  | cons s rest ih =>
      have hs := h s (by simp)
      have ht := ih (fun s hs => h s (by simp [hs]))
      simp only [copiedSlots,List.map_cons,List.sum_cons,List.length_cons] at *
      unfold Snapshot.Valid at hs
      rw [Nat.add_mul,Nat.one_mul]
      have hsUsed : s.used+1 ≤ limit+1 := by omega
      omega

theorem build_copiedSlots {n : Nat} {α : Type u} (produce : Fin n → α) :
    copiedSlots (build produce).2 ≤ (n+1)*(n+1) := by
  have h := copiedSlots_bound n (build produce).2 (build_valid produce)
  rw [build_length] at h
  exact h

end Blotto.NativeArrayCoreControl
