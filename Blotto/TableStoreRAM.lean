import Blotto.RationalCachedTerminalStorage

/-! A typed fixed-region RAM store program for prepared table assignments.
Each instruction updates one existing cell and preserves the outside frame.
The cell-store model refines the retained array patch; it does not assert native
Lean array exclusivity. Address/backend primitive costs are explicit inputs. -/

namespace Blotto

structure TableStoreState (n : ℕ) (α β : Type*) where
  cells : Fin n → α
  frame : β

namespace TableStoreRAM

def store {n : ℕ} {α β : Type*} (j : Fin n) (value : α) (state : TableStoreState n α β) : TableStoreState n α β :=
  ⟨Function.update state.cells j value, state.frame⟩

def run {n : ℕ} {α β : Type*} : List (Fin n × α) → TableStoreState n α β → TableStoreState n α β
  | [], state => state
  | e :: rest, state => run rest (store e.1 e.2 state)

theorem run_append {n : ℕ} {α β : Type*} (first second : List (Fin n × α)) (state : TableStoreState n α β) :
    run (first ++ second) state = run second (run first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons e rest ih => exact ih (store e.1 e.2 state)

theorem store_read {n : ℕ} {α β : Type*} (j : Fin n) (value : α) (state : TableStoreState n α β) (k : Fin n) :
    (store j value state).cells k = if k = j then value else state.cells k := by
  simp only [store, Function.update_apply]

theorem store_frame {n : ℕ} {α β : Type*} (j : Fin n) (value : α) (state : TableStoreState n α β) :
    (store j value state).frame = state.frame := rfl

theorem run_frame {n : ℕ} {α β : Type*} (es : List (Fin n × α)) (state : TableStoreState n α β) :
    (run es state).frame = state.frame := by
  induction es generalizing state with
  | nil => rfl
  | cons e rest ih => exact (ih (store e.1 e.2 state)).trans (store_frame e.1 e.2 state)

theorem store_refines_write {n : ℕ} {α β : Type*} (a : FixedArrayTable n α) (frame : β) (j : Fin n) (value : α) :
    store j value (⟨a.read, frame⟩ : TableStoreState n α β) = ⟨(a.write j value).read, frame⟩ := by
  have hCells : Function.update a.read j value = (a.write j value).read := by
    funext k
    simp only [Function.update_apply, FixedArrayTable.read_write]
  simp only [store, hCells]

theorem run_refines_patch {n : ℕ} {α β : Type*} (es : List (Fin n × α)) (a : FixedArrayTable n α) (frame : β) :
    run es (⟨a.read, frame⟩ : TableStoreState n α β) = ⟨(a.patch es).read, frame⟩ := by
  induction es generalizing a with
  | nil => rfl
  | cons e rest ih =>
    rw [run, store_refines_write, ih, FixedArrayTable.patch]

def fillProgram {n : ℕ} {α : Type*} (value : α) : List (Fin n × α) := List.ofFn (fun j => (j, value))

theorem fillProgram_length {n : ℕ} {α : Type*} (value : α) : (fillProgram (n := n) value).length = n := List.length_ofFn

theorem run_fillProgram {n : ℕ} {α β : Type*} (value : α) (state : TableStoreState n α β) :
    run (fillProgram value) state = ⟨(fun _ => value), state.frame⟩ := by
  let a := FixedArrayTable.ofFn state.cells
  have hCells : a.read = state.cells := by funext j; exact FixedArrayTable.read_ofFn state.cells j
  have hp := run_refines_patch (fillProgram value) a state.frame
  rw [hCells] at hp
  have hRead : ∀ j, (a.patch (fillProgram value)).read j = value := by
    intro j
    apply FixedArrayTable.read_patch_at
    · intro e he _
      rcases List.mem_ofFn.mp he with ⟨k, rfl⟩
      rfl
    · exact List.mem_map.mpr ⟨(j, value), List.mem_ofFn.mpr ⟨j, rfl⟩, rfl⟩
  have hOut : (a.patch (fillProgram value)).read = (fun _ => value) := funext hRead
  rw [hOut] at hp
  exact hp

theorem run_words_bound {n : ℕ} {α β : Type*} (words : α → ℕ) (es : List (Fin n × α))
    (state : TableStoreState n α β) (W : ℕ) (h : ∀ j, words (state.cells j) ≤ W)
    (hAssigned : ∀ e ∈ es, words e.2 ≤ W) : ∀ j, words ((run es state).cells j) ≤ W := by
  induction es generalizing state with
  | nil => exact h
  | cons e rest ih =>
    rw [run]
    apply ih (store e.1 e.2 state)
    · intro j
      rw [store_read]
      split
      · exact hAssigned e (by simp)
      · exact h j
    · intro e he
      exact hAssigned e (List.mem_cons_of_mem _ he)

def writeCount {n : ℕ} {α : Type*} : List (Fin n × α) → ℕ
  | [] => 0
  | _ :: rest => 1 + writeCount rest

theorem writeCount_eq {n : ℕ} {α : Type*} (es : List (Fin n × α)) : writeCount es = es.length := by
  induction es with
  | nil => rfl
  | cons e rest ih => simp only [writeCount, List.length_cons, ih]; omega

theorem region_size {n : ℕ} {α β : Type*} (es : List (Fin n × α)) (state : TableStoreState n α β) :
    Fintype.card (Fin n) = n ∧ (run es state).frame = state.frame := ⟨Fintype.card_fin n, run_frame es state⟩

def writeWordWork {n : ℕ} {α : Type*} (words : α → ℕ) (addressPrice : Fin n → ℕ) : List (Fin n × α) → ℕ
  | [] => 0
  | e :: rest => 2 * words e.2 + addressPrice e.1 + writeWordWork words addressPrice rest

theorem writeWordWork_bound {n : ℕ} {α : Type*} (words : α → ℕ) (addressPrice : Fin n → ℕ)
    (es : List (Fin n × α)) (W A : ℕ) (hWords : ∀ e ∈ es, words e.2 ≤ W)
    (hAddress : ∀ j, addressPrice j ≤ A) : writeWordWork words addressPrice es ≤ es.length * (2 * W + A) := by
  induction es with
  | nil => exact Nat.zero_le _
  | cons e rest ih =>
    have he := hWords e (by simp)
    have ht := ih (fun e he => hWords e (List.mem_cons_of_mem _ he))
    have ha := hAddress e.1
    simp only [writeWordWork, List.length_cons]
    nlinarith

end TableStoreRAM
end Blotto
