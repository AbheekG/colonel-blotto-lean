import Blotto.FairBitKernelBlocks
import Blotto.RejectionKernelTargetLaw
import Blotto.BinaryWidthPrecision

/-! Uniform integers are drawn by actual bounded fair-bit rejection. A block
reads a native Nat rank and rejects ranks outside the positive range. Repeated
blocks stop at the first accepted rank; all-test error is a geometric tail,
independent of the numerical range. Boolean arithmetic pricing is separate. -/

namespace Blotto
open scoped BigOperators Classical
namespace UniformNatRejection

def width (N : ℕ) : ℕ := widthRatioPrecision N 1

def attempt (N : ℕ) (bits : Fin (width N) → Bool) : Option (Fin N) :=
  let rank := (balancedBitIndex (width N) bits).val
  if h : rank < N then some ⟨rank, h⟩ else none

def run (N : ℕ) : (attempts : ℕ) → (Fin (attempts * width N) → Bool) → Option (Fin N)
  | 0, _ => none
  | attempts + 1, bits =>
    let seed : Fin (width N + attempts * width N) → Bool := fun j => bits (j.cast (by ring))
    match attempt N (firstBitBlock (width N) (attempts * width N) seed) with
    | some rank => some rank
    | none => run N attempts (secondBitBlock (width N) (attempts * width N) seed)

def sample (N : ℕ) (hN : 0 < N) (attempts : ℕ) (bits : Fin (attempts * width N) → Bool) : Fin N :=
  (run N attempts bits).getD ⟨0, hN⟩

noncomputable def targetKernel (N : ℕ) (hN : 0 < N) : BoundedExpectationKernel (Fin N) where
  mean := fun f => (1 / (N : ℝ)) * ∑ rank, f rank
  constant := by intro c; simp [ne_of_gt hN]
  monotone := by intro f g h; exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun rank _ => h rank)) (by positivity)
  add := by intro f g; rw [Finset.sum_add_distrib, mul_add]

noncomputable def attemptKernel (N : ℕ) : BoundedExpectationKernel (Option (Fin N)) :=
  (fairBitKernel (width N)).map (attempt N)

def acceptance (N : ℕ) : ℚ := (N : ℚ) / (2 ^ width N : ℕ)

theorem width_upper (N : ℕ) : N ≤ 2 ^ width N := by
  simpa only [width, one_mul] using widthRatioPrecision_bound N 1 (by decide)

theorem width_lower (N : ℕ) (hN : 0 < N) : 2 ^ width N ≤ 2 * N := by
  by_cases hw : width N = 0
  · rw [hw]
    norm_num
    omega
  · have hMinimal := widthRatioPrecision_minimal N 1 (width N - 1) hN (by decide)
    have hFail : ¬N ≤ 2 ^ (width N - 1) := by
      intro h
      have he := hMinimal (by simpa only [one_mul] using h)
      change width N ≤ width N - 1 at he
      omega
    have he : width N - 1 + 1 = width N := by omega
    rw [← he, pow_succ]
    omega

theorem acceptance_bounds (N : ℕ) (hN : 0 < N) : (1 / 2 : ℝ) ≤ (acceptance N : ℝ) ∧ (acceptance N : ℝ) ≤ 1 := by
  have hUpper := width_upper N
  have hLower := width_lower N hN
  have hp : (0 : ℝ) < (2 ^ width N : ℕ) := by positivity
  have hU : (N : ℝ) ≤ (2 ^ width N : ℕ) := by exact_mod_cast hUpper
  have hL : ((2 ^ width N : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hLower
  simp only [acceptance, Rat.cast_div, Rat.cast_natCast]
  constructor
  · exact (le_div_iff₀ hp).mpr (by linarith)
  · exact (div_le_one hp).mpr hU

theorem fairBitKernel_rank_mean (K : ℕ) (test : Fin (2 ^ K) → ℝ) :
    (fairBitKernel K).mean (fun bits => test (balancedBitIndex K bits)) =
      (1 / (2 : ℝ) ^ K) * ∑ rank, test rank := by
  change (∫ bits, test (balancedBitIndex K bits) ∂(fairBitLaw K : MeasureTheory.Measure (Fin K → Bool))) = _
  rw [fairBitLaw_integral_mean]
  simp_rw [balancedBitIndex_eq]
  rw [← Equiv.sum_comp (bitIndexEquiv K)]
  rfl

theorem attemptKernel_mean (N : ℕ) (hN : 0 < N) (f : Option (Fin N) → ℝ) :
    (attemptKernel N).mean f = (acceptance N : ℝ) * (targetKernel N hN).mean (fun rank => f (some rank)) +
      (1 - (acceptance N : ℝ)) * f none := by
  change (fairBitKernel (width N)).mean (fun bits => f (attempt N bits)) = _
  have hRank := fairBitKernel_rank_mean (width N)
    (fun rank => f (if h : rank.val < N then some ⟨rank.val, h⟩ else none))
  apply hRank.trans
  let M := 2 ^ width N
  have hNM : N ≤ M := width_upper N
  have hSplit : (∑ rank : Fin M, f (if h : rank.val < N then some ⟨rank.val, h⟩ else none)) =
      (∑ rank : Fin N, f (some rank)) + ((M - N : ℕ) : ℝ) * f none := by
    have hM : M = N + (M - N) := by omega
    let e : Fin M ≃ Fin N ⊕ Fin (M - N) := (finCongr hM).trans finSumFinEquiv.symm
    let accepted : Fin M → ℝ := fun rank => f (if h : rank.val < N then some ⟨rank.val, h⟩ else none)
    have hEquiv : (∑ rank : Fin M, accepted rank) =
        ∑ rank : Fin N ⊕ Fin (M - N), accepted (e.symm rank) :=
      (Equiv.sum_comp e.symm accepted).symm
    change (∑ rank : Fin M, accepted rank) = _
    rw [hEquiv, Fintype.sum_sum_type]
    have hFirst : (∑ rank : Fin N, accepted (e.symm (Sum.inl rank))) = ∑ rank : Fin N, f (some rank) := by
      apply Finset.sum_congr rfl
      intro rank _
      have hv : (e.symm (Sum.inl rank)).val = rank.val := rfl
      unfold accepted
      simp only [hv, rank.isLt, dite_true]
    have hSecond : (∑ rank : Fin (M - N), accepted (e.symm (Sum.inr rank))) = ((M - N : ℕ) : ℝ) * f none := by
      have he : ∀ rank : Fin (M - N), accepted (e.symm (Sum.inr rank)) = f none := by
        intro rank
        have hv : (e.symm (Sum.inr rank)).val = N + rank.val := rfl
        unfold accepted
        rw [dite_eq_right (by rw [hv]; omega)]
      simp only [he, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    rw [hFirst, hSecond]
  change (1 / (2 : ℝ) ^ width N) * (∑ rank : Fin M, _) = _
  rw [hSplit]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMR : (0 : ℝ) < M := by dsimp only [M]; positivity
  have hDiff : ((M - N : ℕ) : ℝ) = (M : ℝ) - (N : ℝ) := Nat.cast_sub hNM
  simp only [targetKernel, acceptance, Rat.cast_div, Rat.cast_natCast, Nat.cast_pow, Nat.cast_ofNat] at *
  rw [hDiff]
  dsimp only [M] at *
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  field_simp [ne_of_gt hNR]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat]
  ring

theorem run_mean (N attempts : ℕ) (f : Option (Fin N) → ℝ) :
    (fairBitKernel (attempts * width N)).mean (fun bits => f (run N attempts bits)) =
      ((attemptKernel N).firstSuccess attempts).mean f := by
  induction attempts with
  | zero =>
    simp only [run, BoundedExpectationKernel.firstSuccess, BoundedExpectationKernel.point]
    exact (fairBitKernel (0 * width N)).constant (f none)
  | succ attempts ih =>
    have hSize : (attempts + 1) * width N = width N + attempts * width N := by ring
    have hCast := fairBitKernel_cast (width N + attempts * width N) ((attempts + 1) * width N) hSize.symm
      (fun bits => f (run N (attempts + 1) bits))
    apply hCast.symm.trans
    have hSplit := fairBitKernel_blocks (width N) (attempts * width N)
      (fun first rest => f (match attempt N first with | some rank => some rank | none => run N attempts rest))
    apply hSplit.trans
    have hTail : ∀ result : Option (Fin N),
        (fairBitKernel (attempts * width N)).mean (fun bits => f (match result with | some rank => some rank | none => run N attempts bits)) =
        match result with | some rank => f (some rank) | none => ((attemptKernel N).firstSuccess attempts).mean f := by
      intro result
      cases result with
      | none => exact ih
      | some rank =>
        dsimp only
        exact (fairBitKernel _).constant _
    simp_rw [hTail]
    rw [BoundedExpectationKernel.firstSuccess_mean_recurrence]
    change (fairBitKernel (width N)).mean _ = (fairBitKernel (width N)).mean _
    apply congrArg (fairBitKernel (width N)).mean
    funext bits
    dsimp only [BoundedExpectationKernel.point]
    cases attempt N bits <;> rfl

theorem failure_tail (N : ℕ) (hN : 0 < N) (attempts : ℕ) :
    rejectionFailure (acceptance N : ℝ) attempts ≤ 1 / (2 : ℝ) ^ attempts := by
  have ha := acceptance_bounds N hN
  have he := rejectionFailure_mono_probability (by norm_num : (0 : ℝ) ≤ 1 / 2) ha.1 ha.2 attempts
  exact he.trans_eq (by unfold rejectionFailure; rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div_pow])

theorem sample_mean_error (N : ℕ) (hN : 0 < N) (attempts : ℕ) (f : Fin N → ℝ)
    (hf : ∀ rank, 0 ≤ f rank ∧ f rank ≤ 1) :
    |(fairBitKernel (attempts * width N)).mean (fun bits => f (sample N hN attempts bits)) -
      (targetKernel N hN).mean f| ≤ 1 / (2 : ℝ) ^ attempts := by
  have ha := acceptance_bounds N hN
  have he := BoundedExpectationKernel.firstSuccess_fallback_error (attemptKernel N) (targetKernel N hN)
    (acceptance N : ℝ) (by linarith [ha.1]) ha.2 (attemptKernel_mean N hN) attempts ⟨0, hN⟩ f hf
  have hr := run_mean N attempts (fun result => f (result.getD ⟨0, hN⟩))
  change (fairBitKernel (attempts * width N)).mean (fun bits => f (sample N hN attempts bits)) =
    (((attemptKernel N).firstSuccess attempts).map (fun result => result.getD ⟨0, hN⟩)).mean f at hr
  rw [← hr] at he
  exact he.trans (failure_tail N hN attempts)

theorem run_failure_mass (N : ℕ) (hN : 0 < N) (attempts : ℕ) :
    (fairBitKernel (attempts * width N)).mean (fun bits => if run N attempts bits = none then 1 else 0) =
      rejectionFailure (acceptance N : ℝ) attempts := by
  have hr := run_mean N attempts (fun result => if result = none then (1 : ℝ) else 0)
  rw [hr]
  rw [BoundedExpectationKernel.firstSuccess_target_mean (attemptKernel N) (targetKernel N hN)
    (acceptance N : ℝ) (attemptKernel_mean N hN)]
  have ht : (targetKernel N hN).mean (fun rank => if some rank = none then (1 : ℝ) else 0) = 0 := by
    simp only [Option.some_ne_none, ite_false]
    exact (targetKernel N hN).constant 0
  rw [ht]
  simp

end UniformNatRejection
end Blotto
