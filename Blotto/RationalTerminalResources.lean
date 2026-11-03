import Blotto.RationalNestedMidpointLaw
import Blotto.RationalNestedProfileBoxes
import Blotto.RationalAffineAllocation
import Blotto.TerminalResources

/-! Native terminal compilation for three nested resource coordinates.
Focus selection uses two rational fractional tests, and the coordinate
permutation and all conditional input values are computed directly. -/

namespace Blotto
open scoped BigOperators

theorem NestedSpec.eq_of_data (i j : NestedSpec) (hM : i.M = j.M) (ha : i.a = j.a)
    (hd : i.d = j.d) (hc : i.c = j.c) (ht : i.t = j.t) (hq : i.q = j.q) : i = j := by
  cases i
  cases j
  cases hM
  cases ha
  cases hd
  cases hc
  cases ht
  cases hq
  rfl

structure RationalTerminalResources where
  M : ℚ
  long : Fin 3 → ℚ
  short : Fin 3 → ℚ
  resource : Fin 3 → ℚ
  short_pos : ∀ j, 0 < short j
  short_lt : ∀ j, short j < long j
  long_le : ∀ j, long j ≤ M
  box : ∀ j, 0 ≤ resource j ∧ resource j ≤ long j - short j
  fractional_le : (fractionalSet (fun j => ((long j - short j : ℚ) : ℝ)) (fun j => (resource j : ℝ))).card ≤ 1
  mean : (∑ j, (long j - resource j)) = 2 * M

namespace RationalTerminalResources

noncomputable def real (i : RationalTerminalResources) : TerminalResources where
  M := i.M
  long := fun j => i.long j
  short := fun j => i.short j
  resource := fun j => i.resource j
  short_pos := fun j => by exact_mod_cast i.short_pos j
  short_lt := fun j => by exact_mod_cast i.short_lt j
  long_le := fun j => by exact_mod_cast i.long_le j
  box := fun j => by
    change (0 : ℝ) ≤ (i.resource j : ℝ) ∧ (i.resource j : ℝ) ≤ (i.long j : ℝ) - (i.short j : ℝ)
    exact_mod_cast i.box j
  fractional_le := by simpa only [Rat.cast_sub] using i.fractional_le
  mean := by exact_mod_cast i.mean

def capacity (i : RationalTerminalResources) (j : Fin 3) : ℚ := i.long j - i.short j
def weight (i : RationalTerminalResources) (j : Fin 3) : ℚ := i.resource j / i.capacity j
def endpoint (i : RationalTerminalResources) (j : Fin 3) : ℚ := if i.resource j = 0 then i.long j else i.short j
def focus (i : RationalTerminalResources) : Fin 3 :=
  if 0 < i.resource 0 ∧ i.resource 0 < i.capacity 0 then 0 else
    if 0 < i.resource 1 ∧ i.resource 1 < i.capacity 1 then 1 else 2
def permutation (i : RationalTerminalResources) : Equiv.Perm (Fin 3) := Equiv.swap i.focus 2

theorem capacity_real (i : RationalTerminalResources) (j : Fin 3) : (i.capacity j : ℝ) = i.real.capacity j := by
  simp [capacity, real, TerminalResources.capacity]

theorem weight_real (i : RationalTerminalResources) (j : Fin 3) : (i.weight j : ℝ) = i.real.weight j := by
  simp only [weight, Rat.cast_div, i.capacity_real]
  rfl

theorem endpoint_real (i : RationalTerminalResources) (j : Fin 3) : (i.endpoint j : ℝ) = i.real.endpoint j := by
  have he : i.resource j = 0 ↔ i.real.resource j = 0 := by
    change i.resource j = 0 ↔ (i.resource j : ℝ) = 0
    norm_cast
  unfold endpoint TerminalResources.endpoint
  by_cases hz : i.resource j = 0
  · rw [ite_eq_left hz, ite_eq_left (he.mp hz)]
    rfl
  · rw [ite_eq_right hz, ite_eq_right (fun h => hz (he.mpr h))]
    rfl

theorem focus_real (i : RationalTerminalResources) : i.focus = i.real.focus := by
  have he (j : Fin 3) : (0 < i.resource j ∧ i.resource j < i.capacity j) ↔ Fractional i.real.capacity i.real.resource j := by
    dsimp [Fractional, TerminalResources.capacity, real, capacity]
    norm_cast
  unfold focus TerminalResources.focus
  by_cases h0 : 0 < i.resource 0 ∧ i.resource 0 < i.capacity 0
  · rw [ite_eq_left h0, ite_eq_left ((he 0).mp h0)]
  · rw [ite_eq_right h0, ite_eq_right (fun h => h0 ((he 0).mpr h))]
    by_cases h1 : 0 < i.resource 1 ∧ i.resource 1 < i.capacity 1
    · rw [ite_eq_left h1, ite_eq_left ((he 1).mp h1)]
    · rw [ite_eq_right h1, ite_eq_right (fun h => h1 ((he 1).mpr h))]

theorem permutation_real (i : RationalTerminalResources) : i.permutation = i.real.permutation := by
  unfold permutation TerminalResources.permutation
  rw [i.focus_real]

theorem endpoint_bounds (i : RationalTerminalResources) (j : Fin 3) : 0 < i.endpoint j ∧ i.endpoint j ≤ i.M := by
  have h := i.real.endpoint_bounds j
  rw [← i.endpoint_real] at h
  change (0 : ℝ) < (i.endpoint j : ℝ) ∧ (i.endpoint j : ℝ) ≤ (i.M : ℝ) at h
  exact_mod_cast h

theorem weight_bounds (i : RationalTerminalResources) (j : Fin 3) : 0 ≤ i.weight j ∧ i.weight j ≤ 1 := by
  have h := i.real.weight_bounds j
  rw [← i.weight_real] at h
  exact_mod_cast h

def input (i : RationalTerminalResources) : RationalNestedSpec where
  M := i.M
  a := i.endpoint (i.permutation 0)
  d := i.endpoint (i.permutation 1)
  c := i.long i.focus
  t := i.short i.focus
  q := i.weight i.focus
  a_pos := (i.endpoint_bounds _).1
  d_pos := (i.endpoint_bounds _).1
  c_pos := lt_trans (i.short_pos _) (i.short_lt _)
  t_pos := i.short_pos _
  t_lt := i.short_lt _
  q_nonneg := (i.weight_bounds _).1
  q_le := (i.weight_bounds _).2
  a_le := (i.endpoint_bounds _).2
  d_le := (i.endpoint_bounds _).2
  c_le := i.long_le _
  balance := by
    have h : (i.endpoint (i.permutation 0) : ℝ) + (i.endpoint (i.permutation 1) : ℝ) +
        (i.weight i.focus : ℝ) * (i.short i.focus : ℝ) + (1 - (i.weight i.focus : ℝ)) * (i.long i.focus : ℝ) = 2 * (i.M : ℝ) := by
      rw [i.endpoint_real, i.endpoint_real, i.weight_real, i.permutation_real, i.focus_real]
      exact i.real.input.balance
    exact_mod_cast h

theorem input_real (i : RationalTerminalResources) : i.input.real = i.real.input := by
  apply NestedSpec.eq_of_data
  · rfl
  · change (i.endpoint (i.permutation 0) : ℝ) = i.real.endpoint (i.real.permutation 0)
    rw [i.endpoint_real, i.permutation_real]
  · change (i.endpoint (i.permutation 1) : ℝ) = i.real.endpoint (i.real.permutation 1)
    rw [i.endpoint_real, i.permutation_real]
  · change (i.long i.focus : ℝ) = (i.long i.real.focus : ℝ)
    rw [i.focus_real]
  · change (i.short i.focus : ℝ) = (i.short i.real.focus : ℝ)
    rw [i.focus_real]
  · change (i.weight i.focus : ℝ) = i.real.weight i.real.focus
    rw [i.weight_real, i.focus_real]

def profile (i : RationalTerminalResources) (K : ℕ) (outerBits : Fin K → Bool) : RationalSegmentLottery 3 18 :=
  (i.input.profile K outerBits).mapped (RationalAffineAllocation.permutation i.permutation)

end RationalTerminalResources
end Blotto
