import Blotto.BinaryRouteSlot

/-! Valid bounded route assignments compile to fixed-slot bit stores.
Decoded bit memory simulates stores of `some route` in a typed RAM. Initial
slots may be invalid; initialization can therefore overwrite arbitrary bits.
Price/cost and allocation contracts remain separate. -/

namespace Blotto.BinaryRouteStoreProgram

def compile {n m : ℕ} (W : ℕ) : (es : List (Fin n × GroupRoute m)) →
    (∀ e ∈ es, (BinaryRouteFrame.encode e.2).length ≤ W) → List (Fin (n * W) × Bool)
  | [], _ => []
  | e :: rest, hFit => FixedWordStoreRAM.assignments e.1 (BinaryRouteSlot.encode W e.2 (hFit e (by simp))).bit ++
      compile W rest (fun e he => hFit e (List.mem_cons_of_mem _ he))

def decodedCells {n W : ℕ} (m : ℕ) (memory : Fin (n * W) → Bool) : Fin n → Option (GroupRoute m) :=
  fun j => BinaryRouteSlot.read m (fun offset => memory (FixedWordRegion.localAddress j offset))

def optionAssignments {n m : ℕ} (es : List (Fin n × GroupRoute m)) : List (Fin n × Option (GroupRoute m)) :=
  es.map (fun e => (e.1, some e.2))

theorem single_store_decodes {n m W : ℕ} {β : Type*} (e : Fin n × GroupRoute m)
    (hFit : (BinaryRouteFrame.encode e.2).length ≤ W) (memory : Fin (n * W) → Bool) (frame : β) :
    decodedCells m (FixedWordStoreRAM.store e.1 (BinaryRouteSlot.encode W e.2 hFit).bit memory frame).cells =
      (TableStoreRAM.store e.1 (some e.2) (⟨decodedCells m memory, frame⟩ : TableStoreState n (Option (GroupRoute m)) β)).cells := by
  funext j
  rw [TableStoreRAM.store_read]
  by_cases h : j = e.1
  · subst j
    rw [ite_eq_left rfl]
    exact BinaryRouteSlot.stored_readback e.1 e.2 hFit memory frame
  · rw [ite_eq_right h]
    exact BinaryRouteSlot.stored_other_slot e.1 j h e.2 hFit memory frame

theorem compile_decodes {n m W : ℕ} {β : Type*} (es : List (Fin n × GroupRoute m))
    (hFit : ∀ e ∈ es, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : TableStoreState (n * W) Bool β) :
    decodedCells m (TableStoreRAM.run (compile W es hFit) state).cells =
      (TableStoreRAM.run (optionAssignments es)
        (⟨decodedCells m state.cells, state.frame⟩ : TableStoreState n (Option (GroupRoute m)) β)).cells := by
  induction es generalizing state with
  | nil => rfl
  | cons e rest ih =>
    let next := FixedWordStoreRAM.store e.1 (BinaryRouteSlot.encode W e.2 (hFit e (by simp))).bit state.cells state.frame
    have hNext := single_store_decodes e (hFit e (by simp)) state.cells state.frame
    have hFrame := FixedWordStoreRAM.store_frame e.1 (BinaryRouteSlot.encode W e.2 (hFit e (by simp))).bit state.cells state.frame
    rw [compile, TableStoreRAM.run_append]
    change decodedCells m (TableStoreRAM.run (compile W rest _) next).cells = _
    rw [ih]
    rw [hNext, hFrame]
    rfl

theorem compile_length {n m W : ℕ} (es : List (Fin n × GroupRoute m))
    (hFit : ∀ e ∈ es, (BinaryRouteFrame.encode e.2).length ≤ W) :
    (compile W es hFit).length = es.length * W := by
  induction es with
  | nil => simp only [compile, List.length_nil, Nat.zero_mul]
  | cons e rest ih =>
    rw [compile, List.length_append, FixedWordStoreRAM.assignments_length, ih, List.length_cons]
    ring

theorem compile_frame {n m W : ℕ} {β : Type*} (es : List (Fin n × GroupRoute m))
    (hFit : ∀ e ∈ es, (BinaryRouteFrame.encode e.2).length ≤ W) (state : TableStoreState (n * W) Bool β) :
    (TableStoreRAM.run (compile W es hFit) state).frame = state.frame := TableStoreRAM.run_frame _ _

end Blotto.BinaryRouteStoreProgram
