import Blotto.PlayerSpecificSturmEvaluatedRules
import Mathlib.Topology.LocallyConstant.Basic

/-! A proof-only finite-jump identity: a variation count that drops by one
at each root counts the roots between its endpoints. The finite set here
is mathematical semantics, never a numerical root-enumeration primitive. -/
namespace Blotto.PlayerSpecificFiniteJumpCount
open Filter
open scoped Topology BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def prefixCount (S : Finset ℝ) (x : ℝ) : ℕ := ∑ r∈S,if r≤x then 1 else 0

theorem threshold_near (r a : ℝ) (hra : r≠a) : ∀ᶠ x in 𝓝 a,r≤x ↔ r≤a := by
  rcases lt_or_gt_of_ne hra with hlt | hgt
  · have h : ∀ᶠ x in 𝓝 a,r<x := Ioi_mem_nhds hlt
    exact h.mono (fun x hx => ⟨fun _ => hlt.le,fun _ => hx.le⟩)
  · have h : ∀ᶠ x in 𝓝 a,x<r := Iio_mem_nhds hgt
    exact h.mono (fun x hx => ⟨fun h => False.elim ((not_le_of_gt hx) h),
      fun h => False.elim ((not_le_of_gt hgt) h)⟩)

theorem prefix_near (S : Finset ℝ) (a : ℝ) (ha : a∉S) : ∀ᶠ x in 𝓝 a,prefixCount S x=prefixCount S a := by
  have h : ∀ᶠ x in 𝓝 a,∀ r∈S,r≤x ↔ r≤a := by
    apply (eventually_all_finset S).mpr
    intro r hr
    exact threshold_near r a (by intro he; subst r; exact ha hr)
  exact h.mono (fun x hx => by
    unfold prefixCount
    apply Finset.sum_congr rfl
    intro r hr
    simp only [hx r hr])

theorem prefix_remove (S : Finset ℝ) (r x : ℝ) (hr : r∈S) :
    prefixCount S x=prefixCount (S.erase r) x+(if r≤x then 1 else 0) := by
  exact (Finset.sum_erase_add S (fun r => if r≤x then (1 : ℕ) else 0) hr).symm

theorem prefix_interval (S : Finset ℝ) (a b : ℝ) (hab : a≤b) :
    prefixCount S b=prefixCount S a+(S.filter (fun r => a<r ∧ r≤b)).card := by
  have hc : (∑ r∈S,if a<r ∧ r≤b then (1 : ℕ) else 0)=(S.filter (fun r => a<r ∧ r≤b)).card := by
    simp
  rw [← hc]
  unfold prefixCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hra : r≤a
  · have hrb := hra.trans hab
    simp only [hra,hrb,not_lt_of_ge hra,false_and,ite_true,ite_false,add_zero]
  · simp only [hra,lt_of_not_ge hra,true_and,ite_false,zero_add]

def Away (S : Finset ℝ) (V : ℝ → ℕ) : Prop :=
  ∀ a,a∉S → ∀ᶠ x in 𝓝 a,V x=V a

def Jumps (S : Finset ℝ) (V : ℝ → ℕ) : Prop :=
  ∀ a,a∈S → ∀ᶠ x in 𝓝 a,(x<a → V x=V a+1) ∧ (a≤x → V x=V a)

theorem compensated_constant (S : Finset ℝ) (V : ℝ → ℕ) (hAway : Away S V) (hJumps : Jumps S V) :
    IsLocallyConstant (fun x => V x+prefixCount S x) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro a
  by_cases ha : a∈S
  · have hc := prefix_near (S.erase a) a (by simp)
    have hv := hJumps a ha
    filter_upwards [hc,hv] with x hcount hvalue
    rw [prefix_remove S a x ha,prefix_remove S a a ha,hcount]
    simp only [le_refl,ite_true]
    by_cases hx : x<a
    · rw [ite_eq_right (not_le_of_gt hx),add_zero,hvalue.1 hx]
      omega
    · rw [ite_eq_left (le_of_not_gt hx),hvalue.2 (le_of_not_gt hx)]
  · have hc := prefix_near S a ha
    have hv := hAway a ha
    filter_upwards [hc,hv] with x hcount hvalue
    rw [hcount,hvalue]

theorem interval_count (S : Finset ℝ) (V : ℝ → ℕ) (hAway : Away S V) (hJumps : Jumps S V)
    (a b : ℝ) (hab : a≤b) : V a=V b+(S.filter (fun r => a<r ∧ r≤b)).card := by
  have h := (compensated_constant S V hAway hJumps).apply_eq_of_preconnectedSpace a b
  have hc := prefix_interval S a b hab
  omega

theorem interval_count_sub (S : Finset ℝ) (V : ℝ → ℕ) (hAway : Away S V) (hJumps : Jumps S V)
    (a b : ℝ) (hab : a≤b) : V a-V b=(S.filter (fun r => a<r ∧ r≤b)).card := by
  rw [interval_count S V hAway hJumps a b hab,Nat.add_sub_cancel_left]

end Blotto.PlayerSpecificFiniteJumpCount
