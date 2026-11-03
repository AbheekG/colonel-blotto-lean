import Blotto.ArrayStoreRAM
import Blotto.RationalRouteBitStore

/-! The array-backed route builder streams one slot's assignments at a time.
Its execution equals the complete compiled bit-store program. The proof keeps
logical capacity/frame and handles copying writes through the array RAM model;
complete physical allocator and whole-sampler peak space remain separate. -/

namespace Blotto.FixedArrayTable

theorem patch_append {n : ℕ} {α : Type*} (a : FixedArrayTable n α) (first second : List (Fin n × α)) :
    a.patch (first ++ second) = (a.patch first).patch second := by
  induction first generalizing a with
  | nil => rfl
  | cons e rest ih => exact ih (a.write e.1 e.2)

end Blotto.FixedArrayTable

namespace Blotto.ArrayStoreRAM

theorem run_append {n : ℕ} {α β : Type*} (first second : List (Fin n × α)) (state : ArrayStoreState n α β) :
    run (first ++ second) state = run second (run first state) := by
  unfold run
  rw [FixedArrayTable.patch_append]

end Blotto.ArrayStoreRAM

namespace Blotto.BinaryRouteArrayStore

def assignmentPayloadWords {n W : ℕ} (es : List (Fin (n * W) × Bool)) : ℕ :=
  (es.map (fun e => binaryWordWidth e.1.val + 2)).sum

theorem oneSlotAssignmentPayload_bound {n W : ℕ} (j : Fin n) (word : Fin W → Bool) :
    assignmentPayloadWords (FixedWordStoreRAM.assignments j word) ≤ W * (FixedWordRegion.addressWidth 0 n W + 2) := by
  have hPoint : ∀ e : Fin (n * W) × Bool, binaryWordWidth e.1.val + 2 ≤ FixedWordRegion.addressWidth 0 n W + 2 := by
    intro e
    have hWidth := binaryWordWidth_mono (show e.1.val ≤ 0 + n * W + 1 by have he := e.1.isLt; omega)
    exact Nat.add_le_add_right hWidth 2
  unfold assignmentPayloadWords
  calc
    _ ≤ ((FixedWordStoreRAM.assignments j word).map (fun _ => FixedWordRegion.addressWidth 0 n W + 2)).sum :=
      List.sum_le_sum (fun e _ => hPoint e)
    _ = _ := by simp [FixedWordStoreRAM.assignments_length]

def runStream {n m : ℕ} {β : Type*} (W : ℕ) : (es : List (Fin n × GroupRoute m)) →
    (∀ e ∈ es, (BinaryRouteFrame.encode e.2).length ≤ W) → ArrayStoreState (n * W) Bool β → ArrayStoreState (n * W) Bool β
  | [], _, state => state
  | e :: rest, hFit, state =>
      let next := ArrayStoreRAM.run (FixedWordStoreRAM.assignments e.1 (BinaryRouteSlot.encode W e.2 (hFit e (by simp))).bit) state
      runStream W rest (fun e he => hFit e (List.mem_cons_of_mem _ he)) next

theorem runStream_eq_compiled {n m W : ℕ} {β : Type*} (es : List (Fin n × GroupRoute m))
    (hFit : ∀ e ∈ es, (BinaryRouteFrame.encode e.2).length ≤ W) (state : ArrayStoreState (n * W) Bool β) :
    runStream W es hFit state = ArrayStoreRAM.run (BinaryRouteStoreProgram.compile W es hFit) state := by
  induction es generalizing state with
  | nil => rfl
  | cons e rest ih =>
    rw [runStream, ih, BinaryRouteStoreProgram.compile, ArrayStoreRAM.run_append]

theorem runStream_refines {n m W : ℕ} {β : Type*} (es : List (Fin n × GroupRoute m))
    (hFit : ∀ e ∈ es, (BinaryRouteFrame.encode e.2).length ≤ W) (state : ArrayStoreState (n * W) Bool β) :
    ArrayStoreRAM.view (runStream W es hFit state) =
      TableStoreRAM.run (BinaryRouteStoreProgram.compile W es hFit) (ArrayStoreRAM.view state) := by
  rw [runStream_eq_compiled]
  exact ArrayStoreRAM.run_refines _ state

theorem runStream_region {n m W : ℕ} {β : Type*} (es : List (Fin n × GroupRoute m))
    (hFit : ∀ e ∈ es, (BinaryRouteFrame.encode e.2).length ≤ W) (state : ArrayStoreState (n * W) Bool β) :
    (runStream W es hFit state).cells.data.size = n * W ∧ (runStream W es hFit state).frame = state.frame := by
  rw [runStream_eq_compiled]
  exact ArrayStoreRAM.run_region _ state

def peakStorePayloadWords {n m : ℕ} {β : Type*} (W : ℕ) : (es : List (Fin n × GroupRoute m)) →
    (∀ e ∈ es, (BinaryRouteFrame.encode e.2).length ≤ W) → ArrayStoreState (n * W) Bool β → ℕ → ℕ
  | [], _, _, external => external + n * W
  | e :: rest, hFit, state, external =>
      let assignments := FixedWordStoreRAM.assignments e.1 (BinaryRouteSlot.encode W e.2 (hFit e (by simp))).bit
      let next := ArrayStoreRAM.run assignments state
      max (ArrayStoreRAM.peakPatchWords (fun _ : Bool => 1)
          (external + W * (FixedWordRegion.addressWidth 0 n W + 3)) state.cells assignments)
        (peakStorePayloadWords W rest (fun e he => hFit e (List.mem_cons_of_mem _ he)) next external)

theorem peakStorePayloadWords_bound {n m W : ℕ} {β : Type*} (es : List (Fin n × GroupRoute m))
    (hFit : ∀ e ∈ es, (BinaryRouteFrame.encode e.2).length ≤ W) (state : ArrayStoreState (n * W) Bool β) (external : ℕ) :
    peakStorePayloadWords W es hFit state external ≤
      external + W * (FixedWordRegion.addressWidth 0 n W + 3) + 2 * n * W + 1 := by
  induction es generalizing state with
  | nil => unfold peakStorePayloadWords; nlinarith
  | cons e rest ih =>
    have hSlot := ArrayStoreRAM.peakPatchWords_bound (fun _ : Bool => 1)
      (external + W * (FixedWordRegion.addressWidth 0 n W + 3)) state.cells
      (FixedWordStoreRAM.assignments e.1 (BinaryRouteSlot.encode W e.2 (hFit e (by simp))).bit) 1
      (fun _ => le_rfl) (fun _ _ => le_rfl)
    rw [peakStorePayloadWords]
    exact max_le (by nlinarith) (ih _ _)

end Blotto.BinaryRouteArrayStore
