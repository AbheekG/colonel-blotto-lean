import Blotto.BinaryRouteArrayStore

/-! Instrumented execution of the actual streamed route-array updates.
The abstract payload-copy RAM charges every set for reading and writing the
whole current bit array and its new bit. It permits copying on every write;
no native compiler, exclusivity, allocator or GC cost claim is made. Slot
encoding, address formation and control prices remain separately composed. -/

namespace Blotto.ArrayStoreRAM

def runWithCopyWork {n : ℕ} {α β : Type*} (words : α → ℕ) :
    List (Fin n × α) → ArrayStoreState n α β → ArrayStoreState n α β × ℕ
  | [], state => (state, 0)
  | e :: rest, state =>
      let next : ArrayStoreState n α β := ⟨state.cells.write e.1 e.2, state.frame⟩
      let later := runWithCopyWork words rest next
      (later.1, 2 * (state.cells.payloadWordSum words + words e.2) + later.2)

theorem runWithCopyWork_state {n : ℕ} {α β : Type*} (words : α → ℕ)
    (es : List (Fin n × α)) (state : ArrayStoreState n α β) :
    (runWithCopyWork words es state).1 = run es state := by
  induction es generalizing state with
  | nil => rfl
  | cons e rest ih =>
      rw [runWithCopyWork, ih]
      rfl

theorem runWithCopyWork_cost {n : ℕ} {α β : Type*} (words : α → ℕ)
    (es : List (Fin n × α)) (state : ArrayStoreState n α β) :
    (runWithCopyWork words es state).2 = state.cells.patchCopyWork words es := by
  induction es generalizing state with
  | nil => rfl
  | cons e rest ih =>
      rw [runWithCopyWork, ih]
      rfl

theorem runWithCopyWork_bound {n : ℕ} {α β : Type*} (words : α → ℕ)
    (es : List (Fin n × α)) (state : ArrayStoreState n α β) (W : ℕ)
    (hState : ∀ j, words (state.cells.read j) ≤ W) (hAssigned : ∀ e ∈ es, words e.2 ≤ W) :
    (runWithCopyWork words es state).2 ≤ es.length * (2 * (n + 1) * W) := by
  rw [runWithCopyWork_cost]
  exact state.cells.patchCopyWork_bound words es W hState hAssigned

-- Allocation initializes one fixed array. Each initialization write costs
-- one source read and one destination write in the abstract payload RAM.
def allocateWithCopyWork (n : ℕ) {α β : Type*} (words : α → ℕ) (value : α) (frame : β) :
    ArrayStoreState n α β × ℕ := (allocate n value frame, 2 * n * words value)

theorem allocateWithCopyWork_state (n : ℕ) {α β : Type*} (words : α → ℕ) (value : α) (frame : β) :
    (allocateWithCopyWork n words value frame).1 = allocate n value frame := rfl

theorem allocateWithCopyWork_bits (n : ℕ) {β : Type*} (value : Bool) (frame : β) :
    (allocateWithCopyWork n (fun _ : Bool => 1) value frame).2 = 2 * n := by
  simp only [allocateWithCopyWork, Nat.mul_one]

end Blotto.ArrayStoreRAM

namespace Blotto.BinaryRouteArrayStore

def runStreamWithCopyWork {n m : ℕ} {β : Type*} (W : ℕ) :
    (es : List (Fin n × GroupRoute m)) →
    (∀ e ∈ es, (BinaryRouteFrame.encode e.2).length ≤ W) →
    ArrayStoreState (n * W) Bool β → ArrayStoreState (n * W) Bool β × ℕ
  | [], _, state => (state, 0)
  | e :: rest, hFit, state =>
      let assignments := FixedWordStoreRAM.assignments e.1
        (BinaryRouteSlot.encode W e.2 (hFit e (by simp))).bit
      let step := ArrayStoreRAM.runWithCopyWork (fun _ : Bool => 1) assignments state
      let later := runStreamWithCopyWork W rest
        (fun e he => hFit e (List.mem_cons_of_mem _ he)) step.1
      (later.1, step.2 + later.2)

theorem runStreamWithCopyWork_state {n m W : ℕ} {β : Type*}
    (es : List (Fin n × GroupRoute m))
    (hFit : ∀ e ∈ es, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) :
    (runStreamWithCopyWork W es hFit state).1 = runStream W es hFit state := by
  induction es generalizing state with
  | nil => rfl
  | cons e rest ih =>
      simp only [runStreamWithCopyWork, ArrayStoreRAM.runWithCopyWork_state, runStream]
      exact ih _ _

theorem runStreamWithCopyWork_bound {n m W : ℕ} {β : Type*}
    (es : List (Fin n × GroupRoute m))
    (hFit : ∀ e ∈ es, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : ArrayStoreState (n * W) Bool β) :
    (runStreamWithCopyWork W es hFit state).2 ≤ es.length * W * (2 * (n * W + 1)) := by
  induction es generalizing state with
  | nil => exact Nat.zero_le _
  | cons e rest ih =>
      have hStep := ArrayStoreRAM.runWithCopyWork_bound (fun _ : Bool => 1)
        (FixedWordStoreRAM.assignments e.1 (BinaryRouteSlot.encode W e.2 (hFit e (by simp))).bit)
        state 1 (fun _ => le_rfl) (fun _ _ => le_rfl)
      simp only [FixedWordStoreRAM.assignments_length, Nat.mul_one] at hStep
      have hRest := ih (fun e he => hFit e (List.mem_cons_of_mem _ he))
        (ArrayStoreRAM.run (FixedWordStoreRAM.assignments e.1
          (BinaryRouteSlot.encode W e.2 (hFit e (by simp))).bit) state)
      simp only [runStreamWithCopyWork, ArrayStoreRAM.runWithCopyWork_state, List.length_cons]
      exact (Nat.add_le_add hStep hRest).trans_eq (by ring)

def allocateRunStreamWithCopyWork {n m : ℕ} {β : Type*} (W : ℕ)
    (es : List (Fin n × GroupRoute m))
    (hFit : ∀ e ∈ es, (BinaryRouteFrame.encode e.2).length ≤ W) (frame : β) :
    ArrayStoreState (n * W) Bool β × ℕ :=
  let initial := ArrayStoreRAM.allocateWithCopyWork (n * W) (fun _ : Bool => 1) false frame
  let result := runStreamWithCopyWork W es hFit initial.1
  (result.1, initial.2 + result.2)

theorem allocateRunStreamWithCopyWork_state {n m W : ℕ} {β : Type*}
    (es : List (Fin n × GroupRoute m))
    (hFit : ∀ e ∈ es, (BinaryRouteFrame.encode e.2).length ≤ W) (frame : β) :
    (allocateRunStreamWithCopyWork W es hFit frame).1 =
      runStream W es hFit (ArrayStoreRAM.allocate (n * W) false frame) :=
  runStreamWithCopyWork_state es hFit _

theorem allocateRunStreamWithCopyWork_bound {n m W : ℕ} {β : Type*}
    (es : List (Fin n × GroupRoute m))
    (hFit : ∀ e ∈ es, (BinaryRouteFrame.encode e.2).length ≤ W) (frame : β) :
    (allocateRunStreamWithCopyWork W es hFit frame).2 ≤
      2 * n * W + es.length * W * (2 * (n * W + 1)) := by
  have h := runStreamWithCopyWork_bound es hFit (ArrayStoreRAM.allocate (n * W) false frame)
  unfold allocateRunStreamWithCopyWork
  simp only [ArrayStoreRAM.allocateWithCopyWork, Nat.mul_one]
  exact (Nat.add_le_add_left h _).trans_eq (by ring)

end Blotto.BinaryRouteArrayStore
