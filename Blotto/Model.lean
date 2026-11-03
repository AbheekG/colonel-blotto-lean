import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

/-! The two-player common-value model from report §1 and manuscript §1.
Allocations are real vectors; feasibility is an at-most constraint.
No discretization, expected-budget relaxation, or attainment is built in. -/

namespace Blotto

open scoped BigOperators

abbrev Allocation (n : ℕ) := Fin n → ℝ

def Feasible {n : ℕ} (B : ℝ) (x : Allocation n) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∑ j, x j ≤ B

def FullBudget {n : ℕ} (B : ℝ) (x : Allocation n) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∑ j, x j = B

structure Values (n : ℕ) where
  weight : Fin n → ℝ
  positive : ∀ j, 0 < weight j
  normalized : ∑ j, weight j = 1

noncomputable def share (s t : ℝ) : ℝ :=
  if t < s then 1 else if s = t then 1 / 2 else 0

@[simp] theorem share_tie (s : ℝ) : share s s = 1 / 2 := by
  simp [share]

theorem share_nonneg (s t : ℝ) : 0 ≤ share s t := by
  unfold share
  split_ifs <;> norm_num

theorem share_le_one (s t : ℝ) : share s t ≤ 1 := by
  unfold share
  split_ifs <;> norm_num

theorem share_constant_sum (s t : ℝ) : share s t + share t s = 1 := by
  rcases lt_trichotomy s t with h | h | h
  · simp [share, h, not_lt_of_ge (le_of_lt h), ne_of_lt h]
  · subst t
    norm_num
  · simp [share, h, not_lt_of_ge (le_of_lt h), ne_of_lt h]

theorem share_mono_bid {s s' t : ℝ} (h : s ≤ s') : share s t ≤ share s' t := by
  unfold share
  split_ifs <;> try linarith
  exfalso
  have he : s' = t := by linarith
  contradiction

theorem share_antitone_opponent {s t t' : ℝ} (h : t ≤ t') :
    share s t' ≤ share s t := by
  have hm := share_mono_bid (t := s) h
  have h1 := share_constant_sum s t
  have h2 := share_constant_sum s t'
  linarith

noncomputable def payoff {n : ℕ} (v : Values n) (x y : Allocation n) : ℝ :=
  ∑ j, v.weight j * share (x j) (y j)

theorem payoff_nonneg {n : ℕ} (v : Values n) (x y : Allocation n) :
    0 ≤ payoff v x y := by
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (le_of_lt (v.positive j)) (share_nonneg _ _)

theorem payoff_le_one {n : ℕ} (v : Values n) (x y : Allocation n) :
    payoff v x y ≤ 1 := by
  calc
    payoff v x y ≤ ∑ j, v.weight j * 1 :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (share_le_one _ _) (le_of_lt (v.positive j))
    _ = 1 := by simp [v.normalized]

theorem payoff_constant_sum {n : ℕ} (v : Values n) (x y : Allocation n) :
    payoff v x y + payoff v y x = 1 := by
  rw [payoff, payoff, ← Finset.sum_add_distrib]
  simp_rw [← mul_add, share_constant_sum, mul_one]
  exact v.normalized

theorem payoff_mono_bid {n : ℕ} (v : Values n) {x z : Allocation n}
    (h : ∀ j, x j ≤ z j) (y : Allocation n) : payoff v x y ≤ payoff v z y := by
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (share_mono_bid (h j)) (le_of_lt (v.positive j))

noncomputable def complete {n : ℕ} (B : ℝ) (x : Allocation n) (j : Fin n) :
    Allocation n := Function.update x j (x j + (B - ∑ i, x i))

theorem complete_ge {n : ℕ} {B : ℝ} {x : Allocation n} (hx : Feasible B x)
    (j : Fin n) : ∀ i, x i ≤ complete B x j i := by
  intro i
  by_cases h : i = j
  · subst i
    simp only [complete, Function.update_self]
    linarith [hx.2]
  · simp [complete, Function.update_of_ne h]

theorem complete_full {n : ℕ} {B : ℝ} {x : Allocation n} (hx : Feasible B x)
    (j : Fin n) : FullBudget B (complete B x j) := by
  constructor
  · intro i
    exact le_trans (hx.1 i) (complete_ge hx j i)
  · simp only [complete, Finset.sum_update_of_mem (Finset.mem_univ j)]
    have hsum := Finset.sum_sdiff (s₁ := {j}) (s₂ := Finset.univ)
      (f := x) (by simp : ({j} : Finset (Fin n)) ⊆ Finset.univ)
    simp only [Finset.sum_singleton] at hsum
    linarith

theorem fullBudget_feasible {n : ℕ} {B : ℝ} {x : Allocation n}
    (hx : FullBudget B x) : Feasible B x := ⟨hx.1, le_of_eq hx.2⟩

/-- M01 at the pointwise level, including bids that tie at zero. -/
theorem full_spending_dominates {n : ℕ} (v : Values n) {B : ℝ}
    {x : Allocation n} (hx : Feasible B x) (j : Fin n) (y : Allocation n) :
    payoff v x y ≤ payoff v (complete B x j) y :=
  payoff_mono_bid v (complete_ge hx j) y

end Blotto
