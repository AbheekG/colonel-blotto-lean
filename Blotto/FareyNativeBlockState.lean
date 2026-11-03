import Blotto.FareyPreparedDirectAccess
import Blotto.FixedArrayTable

/-! Materialized player block tables initialize once and update only the
observed field. Raw history correspondence is a proof invariant; the native
step never reads or replays history. Array writes use Array.set and may copy
the table: no reference-count uniqueness or unit-cost copy claim is made. -/

namespace Blotto.FareyImplicitTrainer
open Farey ImplicitLeafCounts ProductSecurityTrainer

structure NativeBlockState {m : ℕ} (input : DirectInput m) where
  first : FixedArrayTable m (List Block)
  second : FixedArrayTable m (List Block)
  first_partition : ∀ field, Partition (rankCap input.first.order) (first.read field)
  second_partition : ∀ field, Partition (rankCap input.second.order) (second.read field)
  first_positive : ∀ field, Positive (first.read field)
  second_positive : ∀ field, Positive (second.read field)

namespace NativeBlockState

def initial {m : ℕ} (input : DirectInput m) : NativeBlockState input where
  first := FixedArrayTable.ofFn (fun _ => [⟨0, rankCap input.first.order, 1⟩])
  second := FixedArrayTable.ofFn (fun _ => [⟨0, rankCap input.second.order, 1⟩])
  first_partition := by intro field; simp [FixedArrayTable.read_ofFn, Partition, CoversFrom]
  second_partition := by intro field; simp [FixedArrayTable.read_ofFn, Partition, CoversFrom]
  first_positive := by
    intro field block hb
    have he : block = (⟨0, rankCap input.first.order, 1⟩ : Block) := by simpa [FixedArrayTable.read_ofFn] using hb
    simp [he]
  second_positive := by
    intro field block hb
    have he : block = (⟨0, rankCap input.second.order, 1⟩ : Block) := by simpa [FixedArrayTable.read_ofFn] using hb
    simp [he]

def step {m : ℕ} {input : DirectInput m} (state : NativeBlockState input) (observed : RawObservation m) : NativeBlockState input :=
  let field := observed.2.2
  let firstNew := FareyDirectBlockHistory.update input.first (input.scaleA field) (observed.2.1 field) input.eta input.theta (state.first.read field)
  let secondNew := FareyDirectBlockHistory.update input.second (input.scaleB field) (observed.1 field) input.eta input.theta (state.second.read field)
  { first := state.first.write field firstNew
    second := state.second.write field secondNew
    first_partition := by
      intro j
      rw [FixedArrayTable.read_write]
      split_ifs with he
      · subst j
        exact updateBlocks_partition _ _ (state.first_partition field) _ _ _ _
      · exact state.first_partition j
    second_partition := by
      intro j
      rw [FixedArrayTable.read_write]
      split_ifs with he
      · subst j
        exact updateBlocks_partition _ _ (state.second_partition field) _ _ _ _
      · exact state.second_partition j
    first_positive := by
      intro j
      rw [FixedArrayTable.read_write]
      split_ifs with he
      · subst j
        exact updateBlocks_positive _ (state.first_positive field) _ _ _ _ input.eta_unit input.theta_unit
      · exact state.first_positive j
    second_positive := by
      intro j
      rw [FixedArrayTable.read_write]
      split_ifs with he
      · subst j
        exact updateBlocks_positive _ (state.second_positive field) _ _ _ _ input.eta_unit input.theta_unit
      · exact state.second_positive j }

def Matches {m : ℕ} {input : DirectInput m} (state : NativeBlockState input) (past : List (RawObservation m)) : Prop :=
  (∀ field, state.first.read field = FareyDirectBlockHistory.blocks input.first input.scaleA rawSelected
    (fun _ x => x.2.1 x.2.2) input.eta input.theta past field) ∧
  (∀ field, state.second.read field = FareyDirectBlockHistory.blocks input.second input.scaleB rawSelected
    (fun _ x => x.1 x.2.2) input.eta input.theta past field)

theorem initial_matches {m : ℕ} (input : DirectInput m) : (initial input).Matches [] := by
  constructor <;> intro field <;> exact FixedArrayTable.read_ofFn _ field

theorem step_matches {m : ℕ} {input : DirectInput m} (state : NativeBlockState input) (past : List (RawObservation m))
    (h : state.Matches past) (observed : RawObservation m) : (state.step observed).Matches (observed :: past) := by
  constructor
  · intro field
    change (state.first.write observed.2.2 _).read field = _
    rw [FixedArrayTable.read_write]
    simp only [FareyDirectBlockHistory.blocks, rawSelected]
    by_cases he : field = observed.2.2
    · subst field
      simp only [Function.update_self, h.1, ite_true]
    · rw [ite_eq_right he, Function.update_of_ne he, h.1]
  · intro field
    change (state.second.write observed.2.2 _).read field = _
    rw [FixedArrayTable.read_write]
    simp only [FareyDirectBlockHistory.blocks, rawSelected]
    by_cases he : field = observed.2.2
    · subst field
      simp only [Function.update_self, h.2, ite_true]
    · rw [ite_eq_right he, Function.update_of_ne he, h.2]

theorem step_first_unchanged {m : ℕ} {input : DirectInput m} (state : NativeBlockState input) (observed : RawObservation m)
    (field : Fin m) (he : field ≠ observed.2.2) : (state.step observed).first.read field = state.first.read field := by
  change (state.first.write observed.2.2 _).read field = _
  rw [FixedArrayTable.read_write, ite_eq_right he]

theorem step_second_unchanged {m : ℕ} {input : DirectInput m} (state : NativeBlockState input) (observed : RawObservation m)
    (field : Fin m) (he : field ≠ observed.2.2) : (state.step observed).second.read field = state.second.read field := by
  change (state.second.write observed.2.2 _).read field = _
  rw [FixedArrayTable.read_write, ite_eq_right he]

theorem step_first_length {m : ℕ} {input : DirectInput m} (state : NativeBlockState input) (observed : RawObservation m) :
    ((state.step observed).first.read observed.2.2).length ≤ (state.first.read observed.2.2).length + 2 := by
  change ((state.first.write observed.2.2 _).read observed.2.2).length ≤ _
  simp only [FixedArrayTable.read_write]
  exact updateBlocks_length _ _ _ _ _

theorem step_second_length {m : ℕ} {input : DirectInput m} (state : NativeBlockState input) (observed : RawObservation m) :
    ((state.step observed).second.read observed.2.2).length ≤ (state.second.read observed.2.2).length + 2 := by
  change ((state.second.write observed.2.2 _).read observed.2.2).length ≤ _
  simp only [FixedArrayTable.read_write]
  exact updateBlocks_length _ _ _ _ _

theorem first_history_length {m : ℕ} {input : DirectInput m} (state : NativeBlockState input)
    (past : List (RawObservation m)) (h : state.Matches past) (field : Fin m) :
    (state.first.read field).length ≤ 1 + 2 * genericCount rawSelected past field := by
  rw [h.1 field]
  exact FareyDirectBlockHistory.blocks_length input.first input.scaleA input.scaleA_nonnegative rawSelected
    (fun _ x => x.2.1 x.2.2) input.eta input.theta past field

theorem second_history_length {m : ℕ} {input : DirectInput m} (state : NativeBlockState input)
    (past : List (RawObservation m)) (h : state.Matches past) (field : Fin m) :
    (state.second.read field).length ≤ 1 + 2 * genericCount rawSelected past field := by
  rw [h.2 field]
  exact FareyDirectBlockHistory.blocks_length input.second input.scaleB input.scaleB_nonnegative rawSelected
    (fun _ x => x.1 x.2.2) input.eta input.theta past field

end NativeBlockState
end Blotto.FareyImplicitTrainer
