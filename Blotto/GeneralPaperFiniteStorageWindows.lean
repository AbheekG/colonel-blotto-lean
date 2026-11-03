import Blotto.GeneralPaperActualSnapshotConstructionStorage

/-! Erased finite maxima for native phase windows. Empty callback families
have peak zero; no enumeration, size census or observer runs in the source.
The recursive scope law retains caller frames while releasing each previous
call's temporary payload before the next call. -/
namespace Blotto.GeneralPaperFiniteStorageWindows
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def maximum {α : Type*} [Fintype α] (window : α → ℕ) : ℕ := Finset.univ.sup window

theorem maximum_bound {α : Type*} [Fintype α] (window : α → ℕ) (B : ℕ)
    (hb : ∀ a,window a≤B) : maximum window≤B :=
  Finset.sup_le (fun a _ => hb a)

theorem observed_le_maximum {α : Type*} [Fintype α] (window : α → ℕ) (a : α) :
    window a≤maximum window := Finset.le_sup (Finset.mem_univ a)

theorem maximum_empty {α : Type*} [Fintype α] [IsEmpty α] (window : α → ℕ) : maximum window=0 := by
  exact Nat.eq_zero_of_le_zero (maximum_bound window 0 (fun a => isEmptyElim a))

def scopePeak (base : ℕ) (frame phase : ℕ → ℕ) : ℕ → ℕ
  | 0 => base
  | count+1 => frame (count+1)+max (scopePeak base frame phase count) (phase count)

def stack (frame : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | count+1 => stack frame count+frame (count+1)

theorem scoped_bound (base B : ℕ) (frame phase : ℕ → ℕ) (count : ℕ)
    (hb : base≤B) (hp : ∀ i<count,phase i≤B) : scopePeak base frame phase count≤stack frame count+B := by
  induction count with
  | zero => simpa only [scopePeak,stack,Nat.zero_add] using hb
  | succ count ih =>
    have hprev := ih (fun i hi => hp i (by omega))
    have hnext : phase count≤stack frame count+B := (hp count (by omega)).trans (Nat.le_add_left _ _)
    have hm := max_le hprev hnext
    change frame (count+1)+max _ _≤stack frame count+frame (count+1)+B
    omega

theorem stack_bound (frame : ℕ → ℕ) (F count : ℕ) (hf : ∀ i≤count,frame i≤F) : stack frame count≤count*F := by
  induction count with
  | zero => simp only [stack,Nat.zero_mul,le_refl]
  | succ count ih =>
    have hp := ih (fun i hi => hf i (by omega))
    have hn := hf (count+1) (Nat.le_refl _)
    rw [stack,Nat.add_mul,Nat.one_mul]
    omega

theorem retained_scope_bound (resident base B F : ℕ) (frame phase : ℕ → ℕ) (count : ℕ)
    (hb : base≤B) (hp : ∀ i<count,phase i≤B) (hf : ∀ i≤count,frame i≤F) :
    resident+scopePeak base frame phase count≤resident+count*F+B := by
  have h := scoped_bound base B frame phase count hb hp
  have hs := stack_bound frame F count hf
  omega

end Blotto.GeneralPaperFiniteStorageWindows
