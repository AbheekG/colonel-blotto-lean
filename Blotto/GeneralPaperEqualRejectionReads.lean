import Blotto.GeneralPaperEqualCategoricalSelector
import Blotto.DyadicMidpointDecodeWork

/-! The actual first-success uniform-integer runner with its short-circuit
fresh-bit read observer. The balanced decoder reads every bit of each visited
block. No unvisited suffix is charged as consumed. Expected reads are derived
from the explicit independent finite fair blocks at every truncation. -/
namespace Blotto.GeneralPaperEqualRejectionReads
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 600000
open UniformNatRejection (width attempt)
open GeneralPaperEqualCategoricalIntegerData

structure Result (N : ℕ) where
  output : Option (Fin N)
  reads : ℕ

def run (N : ℕ) : (cap : ℕ) → (Fin (cap * width N) → Bool) → Result N
  | 0, _ => ⟨none, 0⟩
  | cap + 1, fresh =>
    let bits : Fin (width N + cap * width N) → Bool := fun j => fresh (j.cast (by ring))
    match attempt N (firstBitBlock (width N) (cap * width N) bits) with
    | some r => ⟨some r, BinaryPayload.readCount (width N)⟩
    | none =>
      let later := run N cap (secondBitBlock (width N) (cap * width N) bits)
      ⟨later.output, BinaryPayload.readCount (width N) + later.reads⟩

theorem output (N cap : ℕ) (fresh : Fin (cap * width N) → Bool) :
    (run N cap fresh).output = UniformNatRejection.run N cap fresh := by
  induction cap with
  | zero => rfl
  | succ cap ih =>
    unfold run UniformNatRejection.run
    dsimp only
    cases attempt N (firstBitBlock (width N) (cap * width N)
      (fun j => fresh (j.cast (by ring)))) with
    | some r => rfl
    | none => simpa only using ih (secondBitBlock (width N) (cap * width N)
        (fun j => fresh (j.cast (by ring))))

theorem reads_cap (N cap : ℕ) (fresh : Fin (cap * width N) → Bool) :
    (run N cap fresh).reads ≤ cap * width N := by
  induction cap with
  | zero => simp only [run, Nat.zero_mul, le_refl]
  | succ cap ih =>
    unfold run
    dsimp only
    split
    · rw [BinaryPayload.readCount_eq]
      change width N ≤ (cap + 1) * width N
      nlinarith only [Nat.zero_le (cap * width N)]
    · rw [BinaryPayload.readCount_eq]
      have h := ih (secondBitBlock (width N) (cap * width N)
        (fun j => fresh (j.cast (by ring))))
      nlinarith only [h]

theorem reads_mean (N cap : ℕ) (hN : 0 < N) :
    (fairBitKernel (cap * width N)).mean (fun fresh => ((run N cap fresh).reads : ℝ)) =
      (width N : ℝ) * rejectionExpectedAttempts (UniformNatRejection.acceptance N : ℝ) cap := by
  induction cap with
  | zero =>
    simp only [run, rejectionExpectedAttempts, mul_zero, Nat.cast_zero]
    exact (fairBitKernel (0 * width N)).constant 0
  | succ cap ih =>
    have hSize : (cap + 1) * width N = width N + cap * width N := by ring
    have hCast := fairBitKernel_cast (width N + cap * width N) ((cap + 1) * width N)
      hSize.symm (fun fresh => ((run N (cap + 1) fresh).reads : ℝ))
    apply hCast.symm.trans
    have hSplit := fairBitKernel_blocks (width N) (cap * width N)
      (fun first rest => ((match attempt N first with
        | some _ => BinaryPayload.readCount (width N)
        | none => BinaryPayload.readCount (width N) + (run N cap rest).reads : ℕ) : ℝ))
    have hView : ∀ bits : Fin (width N + cap * width N) → Bool,
        (run N (cap + 1) (fun j => bits (j.cast hSize))).reads =
          match attempt N (firstBitBlock (width N) (cap * width N) bits) with
          | some _ => BinaryPayload.readCount (width N)
          | none => BinaryPayload.readCount (width N) +
              (run N cap (secondBitBlock (width N) (cap * width N) bits)).reads := by
      intro bits
      conv => lhs; rw [run]
      dsimp only
      have hBack : (fun j : Fin (width N + cap * width N) =>
          bits ((j.cast hSize.symm).cast hSize)) = bits := by
        funext j
        apply congrArg bits
        apply Fin.ext
        rfl
      rw [hBack]
      cases attempt N (firstBitBlock (width N) (cap * width N) bits) <;> rfl
    simp_rw [hView]
    apply hSplit.trans
    have hTail : ∀ result : Option (Fin N),
        (fairBitKernel (cap * width N)).mean (fun rest =>
          ((match result with
          | some _ => BinaryPayload.readCount (width N)
          | none => BinaryPayload.readCount (width N) + (run N cap rest).reads : ℕ) : ℝ)) =
        (width N : ℝ) + if result = none then
          (width N : ℝ) * rejectionExpectedAttempts (UniformNatRejection.acceptance N : ℝ) cap else 0 := by
      intro result
      cases result with
      | none =>
        simp only [BinaryPayload.readCount_eq, Nat.cast_add, (fairBitKernel _).add,
          (fairBitKernel _).constant, ih, ite_true]
      | some r =>
        simp only [BinaryPayload.readCount_eq, (fairBitKernel _).constant,
          Option.some_ne_none, ite_false, add_zero]
    simp_rw [hTail]
    change (UniformNatRejection.attemptKernel N).mean
      (fun result => (width N : ℝ) + if result = none then
        (width N : ℝ) * rejectionExpectedAttempts (UniformNatRejection.acceptance N : ℝ) cap else 0) = _
    rw [UniformNatRejection.attemptKernel_mean N hN]
    simp only [Option.some_ne_none, ite_false, add_zero,
      (UniformNatRejection.targetKernel N hN).constant, ite_true, rejectionExpectedAttempts]
    ring

theorem expected_reads (N cap : ℕ) (hN : 0 < N) :
    (fairBitKernel (cap * width N)).mean (fun fresh => ((run N cap fresh).reads : ℝ)) ≤
      2 * (width N : ℝ) := by
  rw [reads_mean N cap hN]
  have h := expected_attempts N hN cap
  nlinarith only [h, mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (width N) : (0 : ℝ) ≤ width N)]

theorem categorical_expected_reads {k s : ℕ} (weight : Fin k → ℚ)
    (h : ∀ j, RationalHeight (weight j) s) (cap : ℕ) :
    (fairBitKernel (cap * width (denominator weight))).mean
      (fun fresh => ((run (denominator weight) cap fresh).reads : ℝ)) ≤ 2 * (s * k + 1 : ℕ) := by
  rw [reads_mean _ _ (denominator_pos weight)]
  exact expected_fair_bit_charge weight h cap

end Blotto.GeneralPaperEqualRejectionReads
