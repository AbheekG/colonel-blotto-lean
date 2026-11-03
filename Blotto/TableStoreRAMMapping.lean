import Blotto.TableStoreRAM

/-! Value mappings commute with fixed-region RAM stores and complete runs.
The map need not be injective. This connects decoded optional values with
typed route records while preserving the outside frame. -/

namespace Blotto.TableStoreRAM

def mapState {n : ℕ} {α γ β : Type*} (f : α → γ) (state : TableStoreState n α β) : TableStoreState n γ β :=
  ⟨fun j => f (state.cells j), state.frame⟩

theorem mapState_store {n : ℕ} {α γ β : Type*} (f : α → γ) (j : Fin n) (value : α) (state : TableStoreState n α β) :
    mapState f (store j value state) = store j (f value) (mapState f state) := by
  have hUpdate : (fun k => f (Function.update state.cells j value k)) =
      Function.update (fun k => f (state.cells k)) j (f value) := by
    funext k
    simp only [Function.update_apply]
    by_cases h : k = j <;> simp [h]
  simp only [mapState, store]
  rw [hUpdate]

theorem run_mapState {n : ℕ} {α γ β : Type*} (f : α → γ) (es : List (Fin n × α)) (state : TableStoreState n α β) :
    run (es.map (fun e => (e.1, f e.2))) (mapState f state) = mapState f (run es state) := by
  induction es generalizing state with
  | nil => rfl
  | cons e rest ih =>
    rw [List.map_cons, run]
    change run (rest.map (fun e => (e.1, f e.2))) (store e.1 (f e.2) (mapState f state)) =
      mapState f (run rest (store e.1 e.2 state))
    rw [← mapState_store, ih]

end Blotto.TableStoreRAM
