import Blotto.PRGEquilibrium
import Blotto.RationalResourceMean

/-! Rational PRG inputs initialize native resource states for both players.
Their real interpretation is the maintained canonical normalized game and
exact resource systems, with no supplied partition or coupling descriptor. -/

namespace Blotto
open scoped BigOperators

structure RationalPRGInput (n : ℕ) where
  values : Fin n → ℚ
  positive : ∀ j, 0 < values j
  normalized : (∑ j, values j) = 1
  b : ℚ
  b_pos : 0 < b
  b_le : b ≤ 1
  small_fields : ∀ j, 2 * values j ≤ b

namespace RationalPRGInput

noncomputable def real {n : ℕ} (i : RationalPRGInput n) : PRGInput n where
  values := ⟨(fun j => (i.values j : ℝ)), (fun j => by exact_mod_cast i.positive j), by exact_mod_cast i.normalized⟩
  b := i.b
  b_pos := by exact_mod_cast i.b_pos
  b_le := by exact_mod_cast i.b_le
  small_fields := fun j => by
    change (2 : ℝ) * (i.values j : ℝ) ≤ (i.b : ℝ)
    exact_mod_cast i.small_fields j

def lengths {n : ℕ} (i : RationalPRGInput n) : Fin n → ℚ := fun j => 2 * i.values j
def richInitial {n : ℕ} (i : RationalPRGInput n) : Fin n → ℚ := i.lengths
def poorInitial {n : ℕ} (i : RationalPRGInput n) : Fin n → ℚ := fun j => i.b * i.lengths j

def richState {n : ℕ} (i : RationalPRGInput n) : RationalActiveResources i.lengths :=
  RationalActiveResources.initial i.lengths i.richInitial

def poorState {n : ℕ} (i : RationalPRGInput n) : RationalActiveResources i.lengths :=
  RationalActiveResources.initial i.lengths i.poorInitial

theorem lengths_real {n : ℕ} (i : RationalPRGInput n) :
    (fun j => (i.lengths j : ℝ)) = i.real.richSystem.length := by
  funext j
  simp [lengths, real, PRGInput.richSystem]

theorem richInitial_real {n : ℕ} (i : RationalPRGInput n) :
    (fun j => (i.richInitial j : ℝ)) = i.real.richSystem.initial := i.lengths_real

theorem poorInitial_real {n : ℕ} (i : RationalPRGInput n) :
    (fun j => (i.poorInitial j : ℝ)) = i.real.poorSystem.initial := by
  funext j
  simp [poorInitial, lengths, real, PRGInput.poorSystem]

theorem richState_invariant {n : ℕ} (i : RationalPRGInput n) : RationalResourceInvariant i.lengths 2 i.richState := by
  have he : i.richState.resource.realAllocation = i.real.richSystem.initial := by
    change (RationalResourceArray.ofAllocation i.richInitial).realAllocation = _
    rw [RationalResourceArray.realAllocation_ofAllocation, i.richInitial_real]
  constructor
  · rw [he, i.lengths_real]
    exact i.real.richSystem.initial_box
  · rw [he]
    simpa only [PRGInput.richSystem, mul_one] using i.real.richSystem.initial_sum

theorem poorState_invariant {n : ℕ} (i : RationalPRGInput n) : RationalResourceInvariant i.lengths (2 * (i.b : ℝ)) i.poorState := by
  have he : i.poorState.resource.realAllocation = i.real.poorSystem.initial := by
    change (RationalResourceArray.ofAllocation i.poorInitial).realAllocation = _
    rw [RationalResourceArray.realAllocation_ofAllocation, i.poorInitial_real]
  constructor
  · rw [he, i.lengths_real]
    exact i.real.poorSystem.initial_box
  · rw [he]
    exact i.real.poorSystem.initial_sum

theorem richResource_rank {n : ℕ} (i : RationalPRGInput n) :
    (rationalResourceMachine i.lengths).rank (.ready i.richState) ≤ n - 1 := rationalResourceMachine_initial_rank _ _

theorem poorResource_rank {n : ℕ} (i : RationalPRGInput n) :
    (rationalResourceMachine i.lengths).rank (.ready i.poorState) ≤ n - 1 := rationalResourceMachine_initial_rank _ _

theorem richState_active_empty {n : ℕ} (i : RationalPRGInput n) : i.richState.active = [] := by
  simp [richState, RationalActiveResources.initial, richInitial, RationalResourceArray.allocation_ofAllocation]

theorem richResource_rank_zero {n : ℕ} (i : RationalPRGInput n) :
    (rationalResourceMachine i.lengths).rank (.ready i.richState) = 0 := by
  change i.richState.active.length - 1 = 0
  rw [i.richState_active_empty]
  rfl

theorem richResource_completed {n : ℕ} (i : RationalPRGInput n) (R : ℕ) (bits : Fin R → Bool)
    {result : RationalActiveResources i.lengths}
    (hr : ((rationalResourceMachine i.lengths).run R (.ready i.richState) bits).1 = some result) :
    InBox (fun j => (i.lengths j : ℝ)) result.resource.realAllocation ∧
      (∑ j, result.resource.realAllocation j) = 2 ∧
      (fractionalSet (fun j => (i.lengths j : ℝ)) result.resource.realAllocation).card ≤ 1 :=
  rationalResourceMachine_terminal_contract _ _ _ _ _ i.richState_invariant hr

theorem poorResource_completed {n : ℕ} (i : RationalPRGInput n) (R : ℕ) (bits : Fin R → Bool)
    {result : RationalActiveResources i.lengths}
    (hr : ((rationalResourceMachine i.lengths).run R (.ready i.poorState) bits).1 = some result) :
    InBox (fun j => (i.lengths j : ℝ)) result.resource.realAllocation ∧
      (∑ j, result.resource.realAllocation j) = 2 * (i.b : ℝ) ∧
      (fractionalSet (fun j => (i.lengths j : ℝ)) result.resource.realAllocation).card ≤ 1 :=
  rationalResourceMachine_terminal_contract _ _ _ _ _ i.poorState_invariant hr

end RationalPRGInput
end Blotto
