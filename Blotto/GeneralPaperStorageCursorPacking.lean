import Blotto.GeneralPaperPreparedSourceLifetimeStorage

/-! Erased embeddings of native bounded counters into phase cursors.
Values are preserved exactly, including zero and the final endpoint. Scope
coverage connects every actually reached child to its recursive observer;
no cursor enumeration or validation runs in the algorithm. -/
namespace Blotto.GeneralPaperStorageCursorPacking
open GeneralPaperFiniteStorageWindows
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def counter (cap value : ℕ) (hv : value≤cap) : Fin (cap+1) := ⟨value,Nat.lt_succ_of_le hv⟩

theorem counter_value (cap value : ℕ) (hv : value≤cap) : (counter cap value hv).val=value := rfl

def vector {n : ℕ} (cap : ℕ) (values : Fin n → ℕ) (hv : ∀ i,values i≤cap) : Fin n → Fin (cap+1) :=
  fun i => counter cap (values i) (hv i)

theorem vector_value {n : ℕ} (cap : ℕ) (values : Fin n → ℕ) (hv : ∀ i,values i≤cap) (i : Fin n) :
    (vector cap values hv i).val=values i := rfl

theorem clipped_counter (cap value bound : ℕ) (hv : value≤cap) (hb : value≤bound) :
    min (counter cap value hv).val bound=value := Nat.min_eq_left hb

theorem clipped_index (cap bound : ℕ) (index : Fin (bound+1)) (hc : bound≤cap) :
    (⟨min (counter cap index.val ((Nat.le_of_lt_succ index.isLt).trans hc)).val bound,
      Nat.lt_succ_of_le (Nat.min_le_right ..)⟩ : Fin (bound+1))=index := by
  apply Fin.ext
  exact Nat.min_eq_left (Nat.le_of_lt_succ index.isLt)

theorem scope_base (base : ℕ) (frame phase : ℕ → ℕ) (count : ℕ) : base≤scopePeak base frame phase count := by
  induction count with
  | zero => exact Nat.le_refl _
  | succ count ih =>
    change base≤frame (count+1)+max (scopePeak base frame phase count) (phase count)
    exact ih.trans ((Nat.le_max_left ..).trans (Nat.le_add_left ..))

theorem scope_phase (base : ℕ) (frame phase : ℕ → ℕ) (count index : ℕ) (hi : index<count) :
    phase index≤scopePeak base frame phase count := by
  induction count with
  | zero => omega
  | succ count ih =>
    change phase index≤frame (count+1)+max (scopePeak base frame phase count) (phase count)
    by_cases he : index=count
    · rw [he]
      exact (Nat.le_max_right ..).trans (Nat.le_add_left ..)
    · exact (ih (by omega)).trans ((Nat.le_max_left ..).trans (Nat.le_add_left ..))

theorem scope_frame (base : ℕ) (frame phase : ℕ → ℕ) (count : ℕ) :
    frame (count+1)≤scopePeak base frame phase (count+1) := Nat.le_add_right _ _

end Blotto.GeneralPaperStorageCursorPacking
