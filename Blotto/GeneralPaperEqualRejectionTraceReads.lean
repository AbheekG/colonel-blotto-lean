import Blotto.GeneralPaperEqualRejectionTraceLaw
import Mathlib.Analysis.SpecificLimits.Normed

/-! Exact expected reads of the uncapped operational fair-bit trace measure.
Every valid trace reads its entire rejected prefix, its accepted block and
the midpoint block. The integral is width/acceptance + midpoint bits, so
the native logarithmic fair-read bound has no truncation parameter. -/
namespace Blotto.GeneralPaperEqualRejectionTraceReads
open MeasureTheory Set
open scoped BigOperators Classical ENNReal
set_option autoImplicit false
set_option maxHeartbeats 700000
open GeneralPaperEqualRejectionTraceMeasure
open UniformNatRejection (width acceptance)

def reads (N K : ℕ) (trace : Trace N K) : ℕ := (trace.1 + 1) * width N + K

theorem valid_reads (N K : ℕ) (trace : Trace N K) (h : Good N K trace.1 trace.2) :
    (GeneralPaperEqualRejectionReads.run N trace.1 (priorBits N K trace.1 trace.2)).reads +
      BinaryPayload.readCount (width N) + BinaryPayload.readCount K = reads N K trace := by
  rw [GeneralPaperEqualRejectionPrefix.flat_failure_reads _ _ _ h.1, BinaryPayload.readCount_eq,
    BinaryPayload.readCount_eq]
  unfold reads
  ring

theorem attempts_hasSum (N : ℕ) (hN : 0 < N) :
    HasSum (fun cap : ℕ => ((cap + 1 : ℕ) : ℝ) *
      (rejectionFailure (acceptance N : ℝ) cap * (acceptance N : ℝ))) (1 / (acceptance N : ℝ)) := by
  have ha := UniformNatRejection.acceptance_bounds N hN
  have hp : (0 : ℝ) < acceptance N := by linarith only [ha.1]
  have hn : ‖(1 : ℝ) - acceptance N‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith only [ha.2])]
    linarith only [ha.1]
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hn).mul_right (acceptance N : ℝ)
  simp only [Nat.choose_one_right, sub_sub_cancel] at h
  convert h using 1
  · funext cap
    unfold rejectionFailure
    push_cast
    ring
  · field_simp

theorem read_charge_hasSum (N K : ℕ) (hN : 0 < N) :
    HasSum (fun cap : ℕ => (((cap + 1) * width N + K : ℕ) : ℝ) *
      (rejectionFailure (acceptance N : ℝ) cap * (acceptance N : ℝ)))
      ((width N : ℝ) / (acceptance N : ℝ) + K) := by
  have h0 := (attempts_hasSum N hN).mul_left (width N : ℝ)
  have h1 := (success_mass_hasSum N hN).mul_left (K : ℝ)
  convert h0.add h1 using 1
  · funext cap
    push_cast
    ring
  · ring

theorem expected_reads_exact (N K : ℕ) (hN : 0 < N) :
    (∫⁻ trace, (reads N K trace : ℝ≥0∞) ∂(law N K hN : Measure (Trace N K))) =
      ENNReal.ofReal ((width N : ℝ) / (acceptance N : ℝ) + K) := by
  have ha := UniformNatRejection.acceptance_bounds N hN
  have hs := read_charge_hasSum N K hN
  change (∫⁻ trace, (reads N K trace : ℝ≥0∞)
    ∂GeneralPaperEqualRejectionTraceMeasure.measure N K) = _
  calc
    _ = ∑' cap, (((cap + 1) * width N + K : ℕ) : ℝ≥0∞) * (part N K cap Set.univ) := by
      rw [GeneralPaperEqualRejectionTraceMeasure.measure, lintegral_sum_measure]
      apply tsum_congr
      intro cap
      rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
      change (∫⁻ _bits, ((((cap + 1) * width N + K : ℕ)) : ℝ≥0∞) ∂part N K cap) = _
      exact lintegral_const _
    _ = ∑' cap, ENNReal.ofReal ((((cap + 1) * width N + K : ℕ) : ℝ) *
        (rejectionFailure (acceptance N : ℝ) cap * (acceptance N : ℝ))) := by
      apply tsum_congr
      intro cap
      rw [part_mass N K cap hN]
      have hn : ENNReal.ofReal ((((cap + 1) * width N + K : ℕ) : ℝ)) =
          (((cap + 1) * width N + K : ℕ) : ℝ≥0∞) := ENNReal.ofReal_natCast _
      rw [← hn, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun cap => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
          (rejectionFailure_unit (by linarith only [ha.1]) ha.2 cap).1 (by linarith only [ha.1])))
          hs.summable, hs.tsum_eq]

theorem expected_reads_bound (N K : ℕ) (hN : 0 < N) :
    (∫⁻ trace, (reads N K trace : ℝ≥0∞) ∂(law N K hN : Measure (Trace N K))) ≤
      ENNReal.ofReal (2 * (width N : ℝ) + K) := by
  rw [expected_reads_exact N K hN]
  apply ENNReal.ofReal_le_ofReal
  have ha := UniformNatRejection.acceptance_bounds N hN
  have hp : (0 : ℝ) < acceptance N := by linarith only [ha.1]
  have hi : 1 / (acceptance N : ℝ) ≤ 2 :=
    (div_le_iff₀ hp).mpr (by linarith only [ha.1])
  have hm := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg (width N) : (0 : ℝ) ≤ width N)
  rw [← mul_div_assoc, mul_one] at hm
  linarith only [hm]

end Blotto.GeneralPaperEqualRejectionTraceReads
