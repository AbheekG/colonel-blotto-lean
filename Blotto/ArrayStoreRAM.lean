import Blotto.TableStoreRAM

/-! Array-backed execution refines the fixed-region RAM store program.
Allocation and patching preserve exact logical capacity. Bounds below count
payload words, including simultaneous old/new arrays when a write copies;
physical spare capacity and allocator records remain separate. -/

namespace Blotto

structure ArrayStoreState (n : ℕ) (α β : Type*) where
  cells : FixedArrayTable n α
  frame : β

namespace ArrayStoreRAM

def allocate (n : ℕ) {α β : Type*} (value : α) (frame : β) : ArrayStoreState n α β :=
  ⟨FixedArrayTable.ofFn (fun _ => value), frame⟩

def run {n : ℕ} {α β : Type*} (es : List (Fin n × α)) (state : ArrayStoreState n α β) : ArrayStoreState n α β :=
  ⟨state.cells.patch es, state.frame⟩

def view {n : ℕ} {α β : Type*} (state : ArrayStoreState n α β) : TableStoreState n α β :=
  ⟨state.cells.read, state.frame⟩

theorem allocate_read {n : ℕ} {α β : Type*} (value : α) (frame : β) (j : Fin n) :
    (allocate n value frame).cells.read j = value := FixedArrayTable.read_ofFn _ _

theorem run_refines {n : ℕ} {α β : Type*} (es : List (Fin n × α)) (state : ArrayStoreState n α β) :
    view (run es state) = TableStoreRAM.run es (view state) :=
  (TableStoreRAM.run_refines_patch es state.cells state.frame).symm

theorem run_region {n : ℕ} {α β : Type*} (es : List (Fin n × α)) (state : ArrayStoreState n α β) :
    (run es state).cells.data.size = n ∧ (run es state).frame = state.frame := ⟨(run es state).cells.size, rfl⟩

theorem run_prefix_words {n : ℕ} {α β : Type*} (words : α → ℕ) (es : List (Fin n × α))
    (state : ArrayStoreState n α β) (W : ℕ) (hState : ∀ j, words (state.cells.read j) ≤ W)
    (hAssigned : ∀ e ∈ es, words e.2 ≤ W) (steps : ℕ) :
    (run (es.take steps) state).cells.payloadWordSum words ≤ n * W := by
  apply FixedArrayTable.payloadWordSum_bound
  exact state.cells.patch_words_bound words _ W hState (fun e he => hAssigned e (List.mem_of_mem_take he))

def peakPatchWords {n : ℕ} {α : Type*} (words : α → ℕ) (external : ℕ) (a : FixedArrayTable n α) : List (Fin n × α) → ℕ
  | [] => external + a.payloadWordSum words
  | e :: rest =>
      max (external + a.payloadWordSum words + (a.write e.1 e.2).payloadWordSum words + words e.2)
        (peakPatchWords words external (a.write e.1 e.2) rest)

theorem peakPatchWords_bound {n : ℕ} {α : Type*} (words : α → ℕ) (external : ℕ) (a : FixedArrayTable n α)
    (es : List (Fin n × α)) (W : ℕ) (hState : ∀ j, words (a.read j) ≤ W)
    (hAssigned : ∀ e ∈ es, words e.2 ≤ W) :
    peakPatchWords words external a es ≤ external + (2 * n + 1) * W := by
  induction es generalizing a with
  | nil =>
    have hs := a.payloadWordSum_bound words W hState
    unfold peakPatchWords
    nlinarith
  | cons e rest ih =>
    have he := hAssigned e (by simp)
    have hNext := a.write_words_bound words W hState e.1 e.2 he
    have hCurrent := a.payloadWordSum_bound words W hState
    have hWritten := (a.write e.1 e.2).payloadWordSum_bound words W hNext
    have hRest := ih (a.write e.1 e.2) hNext (fun e he => hAssigned e (List.mem_cons_of_mem _ he))
    rw [peakPatchWords]
    exact max_le (by nlinarith) hRest

end ArrayStoreRAM
end Blotto
