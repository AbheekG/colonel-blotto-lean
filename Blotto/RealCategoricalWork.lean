import Blotto.RealCallbackWork
import Blotto.RealCategoricalLaw

/-! Shared-register categorical arithmetic composes on the actual indexed
path. A nonpositive mass charges its comparison alone. The allowances price
scratch copies conservatively and do not assume resource-list ownership.
Initial table formation and physical controller/container costs are separate. -/

namespace Blotto
open scoped Classical

noncomputable def realCategoricalCallbackCharge {α : Type*} : RealCategoricalState α → ℕ
  | .selected _ => 0
  | .remaining ⟨_head :: _next :: _tail, mass, _, _⟩ =>
    if 0 < mass then RealCategoricalProgram.preparationWork else 1
  | .remaining _ => 0

theorem realCategoricalCallbackCharge_bound {α : Type*} (cursor : RealCategoricalState α) :
    realCategoricalCallbackCharge cursor ≤ 20 := by
  cases cursor with
  | selected value => exact Nat.zero_le _
  | remaining l =>
    cases l with
    | mk items mass hEq hn =>
      cases items with
      | nil => exact Nat.zero_le _
      | cons head rest =>
        cases rest with
        | nil => exact Nat.zero_le _
        | cons next tail =>
          simp only [realCategoricalCallbackCharge]
          split
          · rw [RealCategoricalProgram.preparationWork_eq]
          · decide

noncomputable def realCategoricalArithmeticWork {k : ℕ} (weight : Fin k → ℝ)
    (h : ∀ j, 0 ≤ weight j) (fallback : Fin k) (seed : Fin (k - 1) → ℝ) : ℕ :=
  (realCategoricalMachine fallback).callbackWork realCategoricalCallbackCharge (k - 1) seed
    (.remaining (realWeightTable weight h)) 0 (Nat.zero_le _)

theorem realCategoricalArithmeticWork_bound {k : ℕ} (weight : Fin k → ℝ)
    (h : ∀ j, 0 ≤ weight j) (fallback : Fin k) (seed : Fin (k - 1) → ℝ) :
    realCategoricalArithmeticWork weight h fallback seed ≤ 20 * k := by
  have hw := (realCategoricalMachine fallback).callbackWork_rank realCategoricalCallbackCharge 20
    realCategoricalCallbackCharge_bound (k - 1) seed (.remaining (realWeightTable weight h))
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) fallback.isLt
  simpa [realCategoricalArithmeticWork, realCategoricalMachine, realCategoricalRank,
    realWeightTable, RealWeightList.prepare, Nat.sub_add_cancel (by omega : 1 ≤ k)] using hw

-- Two labels per request: one uniform read and one threshold comparison.
noncomputable def realCategoricalArithmeticAndChoiceWork {k : ℕ} (weight : Fin k → ℝ)
    (h : ∀ j, 0 ≤ weight j) (fallback : Fin k) (seed : Fin (k - 1) → ℝ) : ℕ :=
  realCategoricalArithmeticWork weight h fallback seed +
    2 * ((realCategoricalMachine fallback).run (k - 1) (.remaining (realWeightTable weight h)) seed).2

theorem realCategoricalArithmeticAndChoiceWork_bound {k : ℕ} (weight : Fin k → ℝ)
    (h : ∀ j, 0 ≤ weight j) (fallback : Fin k) (seed : Fin (k - 1) → ℝ) :
    realCategoricalArithmeticAndChoiceWork weight h fallback seed ≤ 22 * k := by
  have hw := realCategoricalArithmeticWork_bound weight h fallback seed
  have hr := (realCategoricalMachine fallback).run_reads_rank (k - 1)
    (.remaining (realWeightTable weight h)) seed
  have hRank : (realCategoricalMachine fallback).rank (.remaining (realWeightTable weight h)) = k - 1 := by
    simp [realCategoricalMachine, realCategoricalRank, realWeightTable, RealWeightList.prepare]
  rw [hRank] at hr
  unfold realCategoricalArithmeticAndChoiceWork
  omega

noncomputable def realCategoricalRegisterCellsCharge {α : Type*} : RealCategoricalState α → ℕ
  | .selected _ => 0
  | .remaining ⟨_head :: _next :: _tail, mass, _, _⟩ =>
    if 0 < mass then RealCategoricalProgram.allocatedRegisterCells else 0
  | .remaining _ => 0

theorem realCategoricalRegisterCellsCharge_bound {α : Type*} (cursor : RealCategoricalState α) :
    realCategoricalRegisterCellsCharge cursor ≤ 9 := by
  cases cursor with
  | selected value => exact Nat.zero_le _
  | remaining l =>
    cases l with
    | mk items mass hEq hn =>
      cases items with
      | nil => exact Nat.zero_le _
      | cons head rest =>
        cases rest with
        | nil => exact Nat.zero_le _
        | cons next tail =>
          simp only [realCategoricalRegisterCellsCharge]
          split
          · rw [RealCategoricalProgram.allocatedRegisterCells_eq]
          · exact Nat.zero_le _

theorem realCategoricalRegisterCells_bound {k : ℕ} (weight : Fin k → ℝ)
    (h : ∀ j, 0 ≤ weight j) (fallback : Fin k) (seed : Fin (k - 1) → ℝ) :
    (realCategoricalMachine fallback).callbackWork realCategoricalRegisterCellsCharge (k - 1) seed
      (.remaining (realWeightTable weight h)) 0 (Nat.zero_le _) ≤ 9 * k := by
  have hw := (realCategoricalMachine fallback).callbackWork_rank realCategoricalRegisterCellsCharge 9
    realCategoricalRegisterCellsCharge_bound (k - 1) seed (.remaining (realWeightTable weight h))
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) fallback.isLt
  simpa [realCategoricalMachine, realCategoricalRank, realWeightTable, RealWeightList.prepare,
    Nat.sub_add_cancel (by omega : 1 ≤ k)] using hw

end Blotto
