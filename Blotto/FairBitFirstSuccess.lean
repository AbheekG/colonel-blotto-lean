import Blotto.FairBitKernelBlocks
import Blotto.FiniteRejectionAttempts

/-! An explicit bounded short-circuit restart rule reads disjoint blocks of
one finite fair vector. Its failure mass and expected number of trial visits
are derived from the block law identity. This is a seed/visit contract; the
operations performed by an individual trial still need their own cost proof. -/

namespace Blotto
open MeasureTheory
open scoped Classical

theorem fairBitKernel_mul (N : ℕ) (c : ℝ) (f : (Fin N → Bool) → ℝ) :
    (fairBitKernel N).mean (fun bits => c * f bits) = c * (fairBitKernel N).mean f := by
  exact integral_const_mul c f

namespace FairBitFirstSuccess

def flat {N k : ℕ} (bits : Fin ((k + 1) * N) → Bool) : Fin (N + k * N) → Bool :=
  fun j => bits (j.cast (by simp only [Nat.add_mul, Nat.one_mul]; omega))

theorem mean_flat (N k : ℕ) (f : (Fin (N + k * N) → Bool) → ℝ) :
    (fairBitKernel ((k + 1) * N)).mean (fun bits => f (flat bits)) =
      (fairBitKernel (N + k * N)).mean f :=
  fairBitKernel_cast _ _ (by simp only [Nat.add_mul, Nat.one_mul]; omega) f

def run {α : Type*} (N : ℕ) (trial : (Fin N → Bool) → Option α) :
    (k : ℕ) → (Fin (k * N) → Bool) → Option α
  | 0, _ => none
  | k + 1, bits =>
      match trial (firstBitBlock N (k * N) (flat bits)) with
      | none => run N trial k (secondBitBlock N (k * N) (flat bits))
      | some value => some value

def visits {α : Type*} (N : ℕ) (trial : (Fin N → Bool) → Option α) :
    (k : ℕ) → (Fin (k * N) → Bool) → ℕ
  | 0, _ => 0
  | k + 1, bits =>
      1 + match trial (firstBitBlock N (k * N) (flat bits)) with
      | none => visits N trial k (secondBitBlock N (k * N) (flat bits))
      | some _ => 0

theorem visits_le_cap {α : Type*} (N : ℕ) (trial : (Fin N → Bool) → Option α)
    (k : ℕ) (bits : Fin (k * N) → Bool) : visits N trial k bits ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [visits]
    split
    · simpa only [Nat.add_comm] using Nat.add_le_add_left (ih _) 1
    · omega

theorem run_sound {α : Type*} (N : ℕ) (trial : (Fin N → Bool) → Option α)
    (P : α → Prop) (hTrial : ∀ bits value, trial bits = some value → P value)
    (k : ℕ) (bits : Fin (k * N) → Bool) (value : α)
    (hResult : run N trial k bits = some value) : P value := by
  induction k with
  | zero => cases hResult
  | succ k ih =>
    rw [run] at hResult
    split at hResult
    · exact ih _ hResult
    · rename_i result hSome
      have hEqual := Option.some.inj hResult
      subst result
      exact hTrial _ value hSome

theorem failure_mean {α : Type*} (N : ℕ) (trial : (Fin N → Bool) → Option α) (k : ℕ) :
    (fairBitKernel (k * N)).mean (fun bits => if run N trial k bits = none then 1 else 0) =
      ((fairBitKernel N).mean (fun bits => if trial bits = none then 1 else 0)) ^ k := by
  let q := (fairBitKernel N).mean (fun bits => if trial bits = none then (1 : ℝ) else 0)
  change _ = q ^ k
  induction k with
  | zero => simp only [run, ite_true, pow_zero, (fairBitKernel _).constant]
  | succ k ih =>
    change (fairBitKernel ((k + 1) * N)).mean (fun bits =>
      if (match trial (firstBitBlock N (k * N) (flat bits)) with
        | none => run N trial k (secondBitBlock N (k * N) (flat bits))
        | some value => some value) = none then 1 else 0) = _
    let test := fun vector => if (match trial (firstBitBlock N (k * N) vector) with
        | none => run N trial k (secondBitBlock N (k * N) vector)
        | some value => some value) = none then (1 : ℝ) else 0
    change (fairBitKernel ((k + 1) * N)).mean (fun bits => test (flat bits)) = _
    rw [mean_flat N k test]
    dsimp only [test]
    rw [fairBitKernel_blocks N (k * N) (fun head tail =>
      if (match trial head with | none => run N trial k tail | some value => some value) = none
        then 1 else 0)]
    have hInner : ∀ head : Fin N → Bool,
        (fairBitKernel (k * N)).mean (fun tail =>
          if (match trial head with | none => run N trial k tail | some value => some value) = none
            then (1 : ℝ) else 0) = q ^ k * (if trial head = none then 1 else 0) := by
      intro head
      cases h : trial head with
      | none => simp only [ite_true, mul_one, ih]
      | some value => simp only [reduceCtorEq, ite_false, mul_zero, (fairBitKernel _).constant]
    simp_rw [hInner]
    rw [fairBitKernel_mul]
    change q ^ k * q = q ^ (k + 1)
    exact (pow_succ q k).symm

theorem visits_mean {α : Type*} (N : ℕ) (trial : (Fin N → Bool) → Option α) (k : ℕ) :
    (fairBitKernel (k * N)).mean (fun bits => (visits N trial k bits : ℝ)) =
      rejectionExpectedAttempts
        (1 - (fairBitKernel N).mean (fun bits => if trial bits = none then 1 else 0)) k := by
  let q := (fairBitKernel N).mean (fun bits => if trial bits = none then (1 : ℝ) else 0)
  change _ = rejectionExpectedAttempts (1 - q) k
  induction k with
  | zero => simp only [visits, Nat.cast_zero, (fairBitKernel _).constant, rejectionExpectedAttempts]
  | succ k ih =>
    change (fairBitKernel ((k + 1) * N)).mean (fun bits =>
      ((1 + match trial (firstBitBlock N (k * N) (flat bits)) with
        | none => visits N trial k (secondBitBlock N (k * N) (flat bits))
        | some _ => 0 : ℕ) : ℝ)) = _
    let test := fun vector => ((1 + match trial (firstBitBlock N (k * N) vector) with
        | none => visits N trial k (secondBitBlock N (k * N) vector)
        | some _ => 0 : ℕ) : ℝ)
    change (fairBitKernel ((k + 1) * N)).mean (fun bits => test (flat bits)) = _
    rw [mean_flat N k test]
    dsimp only [test]
    rw [fairBitKernel_blocks N (k * N) (fun head tail =>
      ((1 + match trial head with | none => visits N trial k tail | some _ => 0 : ℕ) : ℝ))]
    have hInner : ∀ head : Fin N → Bool,
        (fairBitKernel (k * N)).mean (fun tail =>
          ((1 + match trial head with | none => visits N trial k tail | some _ => 0 : ℕ) : ℝ)) =
          1 + rejectionExpectedAttempts (1 - q) k * (if trial head = none then 1 else 0) := by
      intro head
      cases h : trial head with
      | none =>
        simp only [Nat.cast_add, Nat.cast_one, ite_true, mul_one]
        rw [(fairBitKernel _).add, (fairBitKernel _).constant, ih]
      | some value =>
        simp only [reduceCtorEq, ite_false, mul_zero, Nat.cast_one,
          (fairBitKernel _).constant, add_zero]
    simp_rw [hInner]
    rw [(fairBitKernel _).add, (fairBitKernel _).constant, fairBitKernel_mul,
      rejectionExpectedAttempts]
    change 1 + rejectionExpectedAttempts (1 - q) k * q =
      1 + (1 - (1 - q)) * rejectionExpectedAttempts (1 - q) k
    ring

theorem failure_le_quarter_pow {α : Type*} (N : ℕ) (trial : (Fin N → Bool) → Option α)
    (hReject : (fairBitKernel N).mean (fun bits => if trial bits = none then 1 else 0) ≤ 1 / 4)
    (k : ℕ) :
    (fairBitKernel (k * N)).mean (fun bits => if run N trial k bits = none then 1 else 0) ≤
      (1 / 4 : ℝ) ^ k := by
  rw [failure_mean]
  have hUnit := (fairBitKernel N).mean_unit (fun bits => if trial bits = none then 1 else 0)
    (fun bits => by split_ifs <;> norm_num)
  exact pow_le_pow_left₀ hUnit.1 hReject k

theorem visits_mean_le_four_thirds {α : Type*} (N : ℕ) (trial : (Fin N → Bool) → Option α)
    (hReject : (fairBitKernel N).mean (fun bits => if trial bits = none then 1 else 0) ≤ 1 / 4)
    (k : ℕ) :
    (fairBitKernel (k * N)).mean (fun bits => (visits N trial k bits : ℝ)) ≤ 4 / 3 := by
  rw [visits_mean]
  let q := (fairBitKernel N).mean (fun bits => if trial bits = none then (1 : ℝ) else 0)
  have hUnit := (fairBitKernel N).mean_unit (fun bits => if trial bits = none then 1 else 0)
    (fun bits => by split_ifs <;> norm_num)
  have hQ : q ≤ 1 / 4 := hReject
  have hPositive : 0 < 1 - q := by linarith
  have hInverse := rejectionExpectedAttempts_le_inverse hPositive (by dsimp [q]; linarith [hUnit.1]) k
  have hBound : 1 / (1 - q) ≤ 4 / 3 := by
    apply (div_le_iff₀ hPositive).mpr
    linarith
  exact hInverse.trans hBound

end FairBitFirstSuccess
end Blotto
