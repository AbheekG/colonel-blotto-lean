import Blotto.FairBitLaw
import Blotto.MidpointSegments

/-! The concrete rational K-bit midpoint primitive has exactly the finite
midpoint law. Its segment output has the sharp CDF bound and a hard budget
on every bit vector, without an additional random-index oracle. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators

noncomputable def dyadicMidpointLaw (K : ℕ) : ProbabilityMeasure ℝ :=
  (fairBitLaw K).map (fun bits => (dyadicMidpointSample K bits : ℝ))

theorem dyadicMidpointLaw_eq (K : ℕ) :
    dyadicMidpointLaw K = midpointLaw (pow_pos (by decide : 0 < (2 : ℕ)) K) := by
  apply ProbabilityMeasure.toMeasure_injective
  have hrepr : (fairBitLaw K : Measure (Fin K → Bool)) =
      Measure.sum (fun bits => ENNReal.ofReal (1 / (2 : ℝ) ^ K) • Measure.dirac bits) := by
    calc
      _ = Measure.sum (fun bits => (fairBitLaw K : Measure (Fin K → Bool)) {bits} • Measure.dirac bits) :=
        (Measure.sum_smul_dirac _).symm
      _ = _ := by
        congr 1
        funext bits
        rw [fairBitLaw_singleton_realWeight]
  have hf : Measurable (fun bits : Fin K → Bool => (dyadicMidpointSample K bits : ℝ)) := measurable_of_countable _
  change Measure.map (fun bits => (dyadicMidpointSample K bits : ℝ)) (fairBitLaw K : Measure (Fin K → Bool)) = _
  rw [hrepr, Measure.map_sum hf.aemeasurable]
  simp_rw [Measure.map_smul _ hf.aemeasurable, Measure.map_dirac' hf, dyadicMidpointSample_real]
  change Measure.sum (fun bits => ENNReal.ofReal (1 / (2 : ℝ) ^ K) • Measure.dirac (midpoint (bitIndex K bits))) =
    Measure.sum (fun j : Fin (2 ^ K) => ENNReal.ofReal (1 / ((2 ^ K : ℕ) : ℝ)) • Measure.dirac (midpoint j))
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [Measure.sum_fintype, Measure.sum_fintype]
  exact Equiv.sum_comp (bitIndexEquiv K) (fun j => ENNReal.ofReal (1 / (2 : ℝ) ^ K) • Measure.dirac (midpoint j))

theorem dyadicMidpointLaw_CDF_error (K : ℕ) :
    RealCDFClose (dyadicMidpointLaw K) unitUniform (1 / (2 * (2 : ℝ) ^ K)) := by
  rw [dyadicMidpointLaw_eq]
  have he := midpointLaw_CDF_error (pow_pos (by decide : 0 < (2 : ℕ)) K)
  simpa only [RealCDFClose, Nat.cast_pow, Nat.cast_ofNat] using he

noncomputable def dyadicSegmentPoint {n : ℕ} (K : ℕ) (P Q : Allocation n) (bits : Fin K → Bool) : Allocation n :=
  segmentPoint P Q (dyadicMidpointSample K bits)

noncomputable def dyadicSegmentLaw {n : ℕ} (K : ℕ) (P Q : Allocation n) : Mixed n :=
  (fairBitLaw K).map (dyadicSegmentPoint K P Q)

theorem dyadicSegmentLaw_eq {n : ℕ} (K : ℕ) (P Q : Allocation n) :
    dyadicSegmentLaw K P Q = midpointSegmentLaw (pow_pos (by decide : 0 < (2 : ℕ)) K) P Q := by
  apply ProbabilityMeasure.toMeasure_injective
  have he := congrArg (fun ρ : ProbabilityMeasure ℝ => (ρ.map (segmentPoint P Q) : Measure (Allocation n))) (dyadicMidpointLaw_eq K)
  change Measure.map (segmentPoint P Q)
    (Measure.map (fun bits => (dyadicMidpointSample K bits : ℝ)) (fairBitLaw K : Measure (Fin K → Bool))) = _ at he
  rw [Measure.map_map (measurable_segmentPoint P Q) (measurable_of_countable _)] at he
  exact he

theorem dyadicSegmentLaw_CDF_error {n : ℕ} (K : ℕ) (P Q : Allocation n) :
    CDFClose (dyadicSegmentLaw K P Q) (segmentLaw P Q) (1 / (2 * (2 : ℝ) ^ K)) := by
  rw [dyadicSegmentLaw_eq]
  have he := midpointSegmentLaw_CDF_error (pow_pos (by decide : 0 < (2 : ℕ)) K) P Q
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using he

theorem dyadicSegmentPoint_fullBudget {n : ℕ} (K : ℕ) {B : ℝ} {P Q : Allocation n}
    (hP : FullBudget B P) (hQ : FullBudget B Q) (bits : Fin K → Bool) :
    FullBudget B (dyadicSegmentPoint K P Q bits) :=
  segment_fullBudget hP hQ ⟨le_of_lt (dyadicMidpointSample_bounds K bits).1,
    le_of_lt (dyadicMidpointSample_bounds K bits).2⟩

def rationalSegmentPoint {n : ℕ} (P Q : Fin n → ℚ) (t : ℚ) : Fin n → ℚ :=
  fun j => (1 - t) * P j + t * Q j

theorem rationalSegmentPoint_real {n : ℕ} (P Q : Fin n → ℚ) (t : ℚ) :
    (fun j => (rationalSegmentPoint P Q t j : ℝ)) =
      segmentPoint (fun j => (P j : ℝ)) (fun j => (Q j : ℝ)) t := by
  funext j
  simp [rationalSegmentPoint, segmentPoint]

theorem rationalDyadicSegmentPoint_fullBudget {n : ℕ} (K : ℕ) (P Q : Fin n → ℚ) (B : ℝ)
    (hP : FullBudget B (fun j => (P j : ℝ))) (hQ : FullBudget B (fun j => (Q j : ℝ)))
    (bits : Fin K → Bool) :
    FullBudget B (fun j => (rationalSegmentPoint P Q (dyadicMidpointSample K bits) j : ℝ)) := by
  rw [rationalSegmentPoint_real]
  exact dyadicSegmentPoint_fullBudget K hP hQ bits

end Blotto
