import Blotto.RationalLottoSharedRun
import Blotto.CachedWordControllerCounts
import Blotto.SharedResourceLayout
import Blotto.RationalLottoFlatProgram

/-! A visit observer follows the primary one-state source loop and delegates
to actual cached terminal counts at handoff. It counts source preparation too;
it does not infer work from output equality or reuse old serial visit counts. -/

namespace Blotto.RationalLottoResourceSystem

def sharedVisitCount {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (cursor : SharedResourceCursor i.length) (hCursor : i.SharedInvariant cursor)
    (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  match cursor with
  | .ready state => match hp : prepareResourceChoice state with
    | .done value =>
      let terminal : i.PhaseResult := ⟨value, i.shared_done_terminal state hCursor value hp⟩
      let program := (i.terminalData terminal).program K outerBits scalarBits
      1 + (program.machine.cachedCounts N bits (.state program.start) pos hpos).visits
    | .ask p => 1 + i.sharedVisitCount K outerBits scalarBits N bits (SharedResourceCursor.prepared p)
        (i.shared_prepared_invariant state hCursor p hp) pos hpos
  | .coin choice a b hb hab =>
    1 + if hz : a.isZero = true then i.sharedVisitCount K outerBits scalarBits N bits
        (.ready (choice.select false)) (i.choice_select_invariant choice hCursor false) pos hpos else
      if he : a.same b = true then i.sharedVisitCount K outerBits scalarBits N bits
        (.ready (choice.select true)) (i.choice_select_invariant choice hCursor true) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            i.sharedVisitCount K outerBits scalarBits N bits
              (.coin choice next.2 b hb (a.coinStep_normalized b hlt).le) hCursor (pos + 1) (by omega)
          else i.sharedVisitCount K outerBits scalarBits N bits
              (.ready (choice.select (!bits ⟨pos, hRead⟩)))
              (i.choice_select_invariant choice hCursor (!bits ⟨pos, hRead⟩)) (pos + 1) (by omega)
        else 0
termination_by (N - pos, cursor.rank)
decreasing_by
  · apply Prod.Lex.right; exact SharedResourceCursor.prepared_rank_lt state p hp
  · apply Prod.Lex.right; exact SharedResourceCursor.selected_rank_lt choice a b hb hab false
  · apply Prod.Lex.right; exact SharedResourceCursor.selected_rank_lt choice a b hb hab true
  all_goals apply Prod.Lex.left
  all_goals omega

theorem sharedVisitCount_bound {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (cursor : SharedResourceCursor i.length) (hCursor : i.SharedInvariant cursor)
    (pos : ℕ) (hpos : pos ≤ N) :
    i.sharedVisitCount K outerBits scalarBits N bits cursor hCursor pos hpos ≤ 2 * cursor.rank + 2 * (N - pos) + 164 := by
  revert hCursor
  cases hCursorEq : cursor with
  | ready state =>
    intro hCursor
    conv_lhs => unfold sharedVisitCount
    split
    · rename_i value hp
      let terminal : i.PhaseResult := ⟨value, i.shared_done_terminal state hCursor value hp⟩
      let program := (i.terminalData terminal).program K outerBits scalarBits
      have hCounts := (program.machine.indexedCounts_bounds N bits (.state program.start) pos hpos).2
      have hRank := program.rank_le
      have hCached := congrArg ControllerCounts.visits (program.machine.cachedCounts_refines N bits (.state program.start) pos hpos)
      change (program.machine.cachedCounts N bits (.state program.start) pos hpos).visits =
        (program.machine.indexedCounts N bits (.state program.start) pos hpos).visits at hCached
      change 1 + (program.machine.cachedCounts N bits (.state program.start) pos hpos).visits ≤ _
      simp only [WordStateMachine.cursorRank] at hCounts
      omega
    · rename_i p hp
      have h := i.sharedVisitCount_bound K outerBits scalarBits N bits (SharedResourceCursor.prepared p)
        (i.shared_prepared_invariant state hCursor p hp) pos hpos
      have hRank := SharedResourceCursor.prepared_rank_lt state p hp
      omega
  | coin choice a b hb hab =>
    intro hCursor
    conv_lhs => unfold sharedVisitCount
    by_cases hz : a.isZero = true
    · simp only [dite_eq_left hz]
      have h := i.sharedVisitCount_bound K outerBits scalarBits N bits (.ready (choice.select false))
        (i.choice_select_invariant choice hCursor false) pos hpos
      have hRank := SharedResourceCursor.selected_rank_lt choice a b hb hab false
      omega
    · simp only [dite_eq_right hz]
      by_cases he : a.same b = true
      · simp only [dite_eq_left he]
        have h := i.sharedVisitCount_bound K outerBits scalarBits N bits (.ready (choice.select true))
          (i.choice_select_invariant choice hCursor true) pos hpos
        have hRank := SharedResourceCursor.selected_rank_lt choice a b hb hab true
        omega
      · simp only [dite_eq_right he]
        by_cases hRead : pos < N
        · simp only [dite_eq_left hRead]
          by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
          · simp only [ite_eq_left hd]
            have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
            have h := i.sharedVisitCount_bound K outerBits scalarBits N bits
              (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le) hCursor (pos + 1) (by omega)
            have hRank : (SharedResourceCursor.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le).rank =
                (SharedResourceCursor.coin choice a b hb hab).rank := rfl
            rw [hRank] at h
            omega
          · simp only [ite_eq_right hd]
            have h := i.sharedVisitCount_bound K outerBits scalarBits N bits (.ready (choice.select (!bits ⟨pos, hRead⟩)))
              (i.choice_select_invariant choice hCursor (!bits ⟨pos, hRead⟩)) (pos + 1) (by omega)
            have hRank := SharedResourceCursor.selected_rank_lt choice a b hb hab (!bits ⟨pos, hRead⟩)
            omega
        · simp only [dite_eq_right hRead]
          omega
termination_by (N - pos, cursor.rank)
decreasing_by
  all_goals simp only [hCursorEq]
  all_goals first
    | (apply Prod.Lex.right; apply SharedResourceCursor.prepared_rank_lt; assumption)
    | (apply Prod.Lex.right; exact SharedResourceCursor.selected_rank_lt choice a b hb hab false)
    | (apply Prod.Lex.right; exact SharedResourceCursor.selected_rank_lt choice a b hb hab true)
    | (apply Prod.Lex.left; omega)

def sharedPaperVisitCount {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.sharedVisitCount K (secondBitBlock (innerBitBudget n K) K bits)
    (secondBitBlock (coinBitBudget n K) K inner) (coinBitBudget n K) (firstBitBlock (coinBitBudget n K) K inner)
    (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le _)

theorem sharedPaperVisitCount_bound {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) : i.sharedPaperVisitCount K bits ≤ 10 * n + 6 * K + 6166 := by
  have hActive := i.initialState.active_length_le
  have hRank : (SharedResourceCursor.ready i.initialState).rank ≤ 2 * n + 1 := by
    change 2 * (i.initialState.active.length - 1) + 1 ≤ 2 * n + 1
    omega
  have h := i.sharedVisitCount_bound K
    (secondBitBlock (innerBitBudget n K) K bits)
    (secondBitBlock (coinBitBudget n K) K (firstBitBlock (innerBitBudget n K) K bits))
    (coinBitBudget n K) (firstBitBlock (coinBitBudget n K) K (firstBitBlock (innerBitBudget n K) K bits))
    (.ready i.initialState) i.initial_invariant 0 (Nat.zero_le _)
  simp only [Nat.sub_zero] at h
  unfold coinBitBudget at h
  change i.sharedPaperVisitCount K bits ≤ _ at h
  omega

end Blotto.RationalLottoResourceSystem
