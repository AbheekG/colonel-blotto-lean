import Blotto.RationalTerminalResources
import Blotto.RationalResourceMean

/-! Native three-resource inputs, initial array state and certified terminal
data. The terminal constructor uses the proved source invariant and active-list
length; no numerical validity check or rational reconstruction is assumed. -/

namespace Blotto
open scoped BigOperators

theorem NestedResourceSystem.eq_of_data (i j : NestedResourceSystem) (hM : i.M = j.M)
    (hL : i.long = j.long) (hS : i.short = j.short) (hI : i.initial = j.initial) : i = j := by
  cases i
  cases j
  cases hM
  cases hL
  cases hS
  cases hI
  rfl

structure RationalNestedResourceSystem where
  M : ℚ
  long : Fin 3 → ℚ
  short : Fin 3 → ℚ
  initial : Fin 3 → ℚ
  short_pos : ∀ j, 0 < short j
  short_lt : ∀ j, short j < long j
  long_le : ∀ j, long j ≤ M
  initial_box : ∀ j, 0 ≤ initial j ∧ initial j ≤ long j - short j
  initial_mean : (∑ j, (long j - initial j)) = 2 * M

namespace RationalNestedResourceSystem

def capacity (i : RationalNestedResourceSystem) (j : Fin 3) : ℚ := i.long j - i.short j
def totalResource (i : RationalNestedResourceSystem) : ℚ := ∑ j, i.initial j
def initialState (i : RationalNestedResourceSystem) : RationalActiveResources i.capacity :=
  RationalActiveResources.initial i.capacity i.initial

noncomputable def real (i : RationalNestedResourceSystem) : NestedResourceSystem where
  M := i.M
  long := fun j => i.long j
  short := fun j => i.short j
  initial := fun j => i.initial j
  short_pos := fun j => by exact_mod_cast i.short_pos j
  short_lt := fun j => by exact_mod_cast i.short_lt j
  long_le := fun j => by exact_mod_cast i.long_le j
  initial_box := fun j => by
    change (0 : ℝ) ≤ (i.initial j : ℝ) ∧ (i.initial j : ℝ) ≤ (i.long j : ℝ) - (i.short j : ℝ)
    exact_mod_cast i.initial_box j
  initial_mean := by exact_mod_cast i.initial_mean

theorem capacity_real (i : RationalNestedResourceSystem) (j : Fin 3) :
    (i.capacity j : ℝ) = i.real.capacity j := by simp [capacity, real, NestedResourceSystem.capacity]

theorem initialState_allocation (i : RationalNestedResourceSystem) : i.initialState.resource.allocation = i.initial := by
  exact RationalResourceArray.allocation_ofAllocation i.initial

theorem initial_invariant (i : RationalNestedResourceSystem) :
    RationalResourceInvariant i.capacity (i.totalResource : ℝ) i.initialState := by
  constructor
  · intro j
    change (0 : ℝ) ≤ (i.initialState.resource.allocation j : ℝ) ∧
      (i.initialState.resource.allocation j : ℝ) ≤ (i.capacity j : ℝ)
    rw [i.initialState_allocation]
    exact_mod_cast i.initial_box j
  · change (∑ j, (i.initialState.resource.allocation j : ℝ)) = (i.totalResource : ℝ)
    rw [i.initialState_allocation]
    simp [totalResource]

def terminal (i : RationalNestedResourceSystem) (s : RationalActiveResources i.capacity)
    (hs : RationalResourceInvariant i.capacity (i.totalResource : ℝ) s) (ht : s.active.length ≤ 1) : RationalTerminalResources where
  M := i.M
  long := i.long
  short := i.short
  resource := s.resource.allocation
  short_pos := i.short_pos
  short_lt := i.short_lt
  long_le := i.long_le
  box := fun j => by
    have h := hs.1 j
    change (0 : ℝ) ≤ (s.resource.allocation j : ℝ) ∧ (s.resource.allocation j : ℝ) ≤ (i.capacity j : ℝ) at h
    exact_mod_cast h
  fractional_le := by
    have he := s.realView.length_eq_card
    change s.active.length = (fractionalSet (fun j => (i.capacity j : ℝ)) s.resource.realAllocation).card at he
    change (fractionalSet (fun j => (i.capacity j : ℝ)) s.resource.realAllocation).card ≤ 1
    omega
  mean := by
    have h : (∑ j, s.resource.allocation j) = i.totalResource := by
      have hR := hs.2
      change (∑ j, (s.resource.allocation j : ℝ)) = (i.totalResource : ℝ) at hR
      exact_mod_cast hR
    rw [Finset.sum_sub_distrib, h]
    simpa only [Finset.sum_sub_distrib, totalResource] using i.initial_mean

theorem initial_rank (i : RationalNestedResourceSystem) :
    (rationalResourceMachine i.capacity).rank (.ready i.initialState) ≤ 2 :=
  rationalResourceMachine_initial_rank i.capacity i.initial

end RationalNestedResourceSystem
end Blotto
