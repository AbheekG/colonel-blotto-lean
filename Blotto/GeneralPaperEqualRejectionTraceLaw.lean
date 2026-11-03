import Blotto.GeneralPaperEqualRejectionTraceMeasure

/-! Exact uncapped allocation law obtained by decoding the fair-bit
first-success trace measure. Every positive-mass trace is terminating; the
default value on invalid traces has measure zero and is never a fallback
of the sampling algorithm. -/
namespace Blotto.GeneralPaperEqualRejectionTraceLaw
open MeasureTheory Set
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 700000
open GeneralPaperEqualRejectionTraceMeasure
open GeneralPaperEqualCategoricalIntegerData
open GeneralPaperEqualRejectionAllocation (emit target)

def decode {n m k : ℕ} (G : RationalProportionalGroups n m) (l : RationalSegmentLottery m k)
    (K : ℕ) (trace : Trace (denominator l.weight) K) : Fin n → ℚ :=
  match UniformNatRejection.attempt (denominator l.weight)
      (last (denominator l.weight) K trace.1 trace.2) with
  | none => fun _ => 0
  | some r => emit G l K (GeneralPaperEqualCategoricalSelector.rank l.weight l.nonnegative l.mass r)
      (scalar (denominator l.weight) K trace.1 trace.2)

theorem decode_fullBudget {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (K : ℕ) (B : ℚ)
    (hb : ∀ slot, FullBudget (B : ℝ) (l.real.P slot) ∧ FullBudget (B : ℝ) (l.real.Q slot))
    (trace : Trace (denominator l.weight) K) (h : Good (denominator l.weight) K trace.1 trace.2) :
    FullBudget (B : ℝ) (fun j => (decode G l K trace j : ℝ)) := by
  unfold Good at h
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h.2
  unfold decode
  rw [hr]
  exact G.split_fullBudget (l.point_fullBudget K hb _ _)

theorem level_event_test {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (K cap : ℕ) (A : Set (Allocation n))
    (bits : Fin (length (denominator l.weight) K cap) → Bool) :
    test (denominator l.weight) K cap
      (fun r scalar => if (fun j => (emit G l K
        (GeneralPaperEqualCategoricalSelector.rank l.weight l.nonnegative l.mass r) scalar j : ℝ)) ∈ A then 1 else 0) bits =
      if Good (denominator l.weight) K cap bits ∧
        (fun j => (decode G l K ⟨cap, bits⟩ j : ℝ)) ∈ A then (1 : ℝ) else 0 := by
  unfold test Good decode
  by_cases hp : (GeneralPaperEqualRejectionReads.run (denominator l.weight) cap
      (priorBits (denominator l.weight) K cap bits)).output = none
  · simp only [hp, ite_true, true_and]
    cases UniformNatRejection.attempt (denominator l.weight) (last (denominator l.weight) K cap bits) <;> simp
  · simp only [hp, ite_false, false_and]

theorem part_event {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (K cap : ℕ) (A : Set (Allocation n)) (hA : MeasurableSet A) :
    (part (denominator l.weight) K cap)
      {bits | (fun j => (decode G l K ⟨cap, bits⟩ j : ℝ)) ∈ A} =
      ENNReal.ofReal (rejectionFailure (UniformNatRejection.acceptance (denominator l.weight) : ℝ) cap *
        (UniformNatRejection.acceptance (denominator l.weight) : ℝ) *
        (target G l K : Measure (Allocation n)).real A) := by
  let N := denominator l.weight
  have h := level_mean N K cap (denominator_pos l.weight)
    (fun r scalar => if (fun j => (emit G l K
      (GeneralPaperEqualCategoricalSelector.rank l.weight l.nonnegative l.mass r) scalar j : ℝ)) ∈ A then 1 else 0)
  rw [GeneralPaperEqualCategoricalSelector.rank_mean l.weight l.nonnegative l.mass
    (fun slot => (fairBitKernel K).mean
      (fun scalar => if (fun j => (emit G l K slot scalar j : ℝ)) ∈ A then 1 else 0))] at h
  rw [← GeneralPaperEqualRejectionAllocation.target_event G l K A hA] at h
  have ht : test N K cap
      (fun r scalar => if (fun j => (emit G l K
        (GeneralPaperEqualCategoricalSelector.rank l.weight l.nonnegative l.mass r) scalar j : ℝ)) ∈ A then 1 else 0) =
      fun bits => if bits ∈ {bits | (fun j => (decode G l K ⟨cap, bits⟩ j : ℝ)) ∈ A} ∩
        {bits | Good N K cap bits} then 1 else 0 := by
    funext bits
    rw [level_event_test]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_comm]
    rfl
  rw [ht] at h
  have hf := GeneralPaperEqualRejectionAllocation.fair_event (length N K cap)
    ({bits | (fun j => (decode G l K ⟨cap, bits⟩ j : ℝ)) ∈ A} ∩ {bits | Good N K cap bits})
  have hReal : (fairBitLaw (length N K cap) : Measure (Fin (length N K cap) → Bool)).real
      ({bits | (fun j => (decode G l K ⟨cap, bits⟩ j : ℝ)) ∈ A} ∩ {bits | Good N K cap bits}) =
      rejectionFailure (UniformNatRejection.acceptance N : ℝ) cap *
        (UniformNatRejection.acceptance N : ℝ) * (target G l K : Measure (Allocation n)).real A := by
    rw [hf]
    convert h using 1
    apply congrArg (fairBitKernel (length N K cap)).mean
    funext bits
    split_ifs <;> rfl
  unfold part
  rw [Measure.restrict_apply (Set.toFinite _).measurableSet, ← hReal]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

noncomputable def outputLaw {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (K : ℕ) : Mixed n :=
  (law (denominator l.weight) K (denominator_pos l.weight)).map
    (fun trace j => (decode G l K trace j : ℝ))

theorem outputLaw_eq {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (K : ℕ) : outputLaw G l K = target G l K := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro A hA
  change (Measure.map (fun trace j => (decode G l K trace j : ℝ))
    (GeneralPaperEqualRejectionTraceMeasure.measure (denominator l.weight) K)) A = (target G l K : Measure (Allocation n)) A
  rw [Measure.map_apply (measurable_of_countable _) hA, GeneralPaperEqualRejectionTraceMeasure.measure,
    Measure.sum_apply _ (hA.preimage (measurable_of_countable _))]
  simp_rw [Measure.map_apply (measurable_of_countable _) (hA.preimage (measurable_of_countable _))]
  change (∑' cap, part (denominator l.weight) K cap
    {bits | (fun j => (decode G l K ⟨cap, bits⟩ j : ℝ)) ∈ A}) = _
  simp_rw [part_event G l K _ A hA]
  have hs := (success_mass_hasSum (denominator l.weight) (denominator_pos l.weight)).mul_right
    ((target G l K : Measure (Allocation n)).real A)
  have ha := UniformNatRejection.acceptance_bounds (denominator l.weight) (denominator_pos l.weight)
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun cap => mul_nonneg (mul_nonneg
      (rejectionFailure_unit (by linarith only [ha.1]) ha.2 cap).1 (by linarith only [ha.1]))
      (measureReal_nonneg)) hs.summable, hs.tsum_eq, one_mul]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem outputs_fullBudget_ae {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (K : ℕ) (B : ℚ)
    (hb : ∀ slot, FullBudget (B : ℝ) (l.real.P slot) ∧ FullBudget (B : ℝ) (l.real.Q slot)) :
    ∀ᵐ trace ∂(law (denominator l.weight) K (denominator_pos l.weight) :
      Measure (Trace (denominator l.weight) K)), FullBudget (B : ℝ) (fun j => (decode G l K trace j : ℝ)) :=
  (good_ae _ _ (denominator_pos l.weight)).mono fun trace h => decode_fullBudget G l K B hb trace h

end Blotto.GeneralPaperEqualRejectionTraceLaw
