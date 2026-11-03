import Blotto.GeneralPaperEqualRejectionReads
import Blotto.GeneralPaperEqualRoundedBoundary
import Blotto.RationalSegmentIdealEvent
import Blotto.FiniteMixturePayoff

/-! Rational grouped midpoint emission after exact denominator rejection.
Finite truncations preserve failure rather than execute a fallback. Their
completed-output event law is the success mass times the precise midpoint
allocation law; every completed output is a feasible whole allocation. -/
namespace Blotto.GeneralPaperEqualRejectionAllocation
open MeasureTheory
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 700000
open GeneralPaperEqualCategoricalIntegerData

def emit {n m k : ℕ} (G : RationalProportionalGroups n m) (l : RationalSegmentLottery m k)
    (K : ℕ) (slot : Fin k) (scalar : Fin K → Bool) : Fin n → ℚ :=
  G.split (l.point K slot scalar)

noncomputable def target {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (K : ℕ) : Mixed n :=
  G.real.splitLaw (l.real.dyadicLaw K)

theorem fair_event (K : ℕ) (A : Set (Fin K → Bool)) :
    (fairBitLaw K : Measure (Fin K → Bool)).real A =
      (fairBitKernel K).mean (fun bits => if bits ∈ A then (1 : ℝ) else 0) := by
  symm
  change (∫ bits, (if bits ∈ A then (1 : ℝ) else 0)
    ∂(fairBitLaw K : Measure (Fin K → Bool))) = _
  have he : (fun bits => if bits ∈ A then (1 : ℝ) else 0) = A.indicator 1 := by
    funext bits
    simp only [Set.indicator_apply, Pi.one_apply]
  rw [he]
  exact integral_indicator_one (Set.toFinite A).measurableSet

theorem target_event {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (K : ℕ) (A : Set (Allocation n)) (hA : MeasurableSet A) :
    (target G l K : Measure (Allocation n)).real A =
      ∑ slot, (l.weight slot : ℝ) * (fairBitKernel K).mean
        (fun scalar => if (fun j => (emit G l K slot scalar j : ℝ)) ∈ A then (1 : ℝ) else 0) := by
  change (Measure.map G.real.split (l.real.dyadicLaw K : Measure (Allocation m))).real A = _
  rw [map_measureReal_apply G.real.measurable_split hA]
  unfold SegmentLottery.dyadicLaw
  rw [probabilityMixture_real_apply _ _ _ _ _ (hA.preimage G.real.measurable_split)]
  apply Finset.sum_congr rfl
  intro slot _
  congr 1
  change (Measure.map (dyadicSegmentPoint K (l.real.P slot) (l.real.Q slot))
    (fairBitLaw K : Measure (Fin K → Bool))).real (G.real.split ⁻¹' A) = _
  rw [map_measureReal_apply (measurable_of_countable _) (hA.preimage G.real.measurable_split), fair_event]
  apply congrArg (fairBitKernel K).mean
  funext scalar
  have he : (fun j => (emit G l K slot scalar j : ℝ)) =
      G.real.split (dyadicSegmentPoint K (l.real.P slot) (l.real.Q slot) scalar) := by
    rw [emit, G.split_real, l.point_real]
    rfl
  rw [he]
  rfl

structure Result (n : ℕ) where
  output : Option (Fin n → ℚ)
  reads : ℕ

def run {n m k : ℕ} (G : RationalProportionalGroups n m) (l : RationalSegmentLottery m k)
    (cap K : ℕ) (fresh : Fin (cap * UniformNatRejection.width (denominator l.weight) + K) → Bool) : Result n :=
  let R := cap * UniformNatRejection.width (denominator l.weight)
  let choice := GeneralPaperEqualRejectionReads.run (denominator l.weight) cap (firstBitBlock R K fresh)
  match choice.output with
  | none => ⟨none, choice.reads⟩
  | some r =>
    let slot := GeneralPaperEqualCategoricalSelector.rank l.weight l.nonnegative l.mass r
    ⟨some (emit G l K slot (secondBitBlock R K fresh)), choice.reads + BinaryPayload.readCount K⟩

theorem output {n m k : ℕ} (G : RationalProportionalGroups n m) (l : RationalSegmentLottery m k)
    (cap K : ℕ) (fresh : Fin (cap * UniformNatRejection.width (denominator l.weight) + K) → Bool) :
    (run G l cap K fresh).output =
      (GeneralPaperEqualCategoricalSelector.run l.weight l.nonnegative l.mass cap
        (firstBitBlock (cap * UniformNatRejection.width (denominator l.weight)) K fresh)).map
        (fun slot => emit G l K slot
          (secondBitBlock (cap * UniformNatRejection.width (denominator l.weight)) K fresh)) := by
  unfold run GeneralPaperEqualCategoricalSelector.run
  dsimp only
  have he := GeneralPaperEqualRejectionReads.output (denominator l.weight) cap
    (firstBitBlock (cap * UniformNatRejection.width (denominator l.weight)) K fresh)
  rw [← he]
  cases (GeneralPaperEqualRejectionReads.run (denominator l.weight) cap
    (firstBitBlock (cap * UniformNatRejection.width (denominator l.weight)) K fresh)).output <;> rfl

theorem completed_fullBudget {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (cap K : ℕ) (B : ℚ)
    (hb : ∀ slot, FullBudget (B : ℝ) (l.real.P slot) ∧ FullBudget (B : ℝ) (l.real.Q slot))
    (fresh : Fin (cap * UniformNatRejection.width (denominator l.weight) + K) → Bool)
    (row : Fin n → ℚ) (h : (run G l cap K fresh).output = some row) :
    FullBudget (B : ℝ) (fun j => (row j : ℝ)) := by
  rw [output] at h
  obtain ⟨slot, _, he⟩ := Option.map_eq_some_iff.mp h
  subst row
  exact G.split_fullBudget (l.point_fullBudget K hb slot _)

theorem reads_le {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (cap K : ℕ)
    (fresh : Fin (cap * UniformNatRejection.width (denominator l.weight) + K) → Bool) :
    (run G l cap K fresh).reads ≤
      (GeneralPaperEqualRejectionReads.run (denominator l.weight) cap
        (firstBitBlock (cap * UniformNatRejection.width (denominator l.weight)) K fresh)).reads + K := by
  unfold run
  dsimp only
  split <;> simp only [BinaryPayload.readCount_eq] <;> omega

theorem mean_commute (R K : ℕ) (f : (Fin R → Bool) → (Fin K → Bool) → ℝ) :
    (fairBitKernel R).mean (fun a => (fairBitKernel K).mean (fun b => f a b)) =
      (fairBitKernel K).mean (fun b => (fairBitKernel R).mean (fun a => f a b)) := by
  exact integral_integral_swap Integrable.of_finite

theorem mean_mul (K : ℕ) (a : ℝ) (f : (Fin K → Bool) → ℝ) :
    (fairBitKernel K).mean (fun b => a * f b) = a * (fairBitKernel K).mean f :=
  integral_const_mul a f

theorem mean_weighted {k : ℕ} (K : ℕ) (w : Fin k → ℝ) (f : Fin k → (Fin K → Bool) → ℝ) :
    (fairBitKernel K).mean (fun b => ∑ j, w j * f j b) =
      ∑ j, w j * (fairBitKernel K).mean (f j) := by
  change (∫ b, ∑ j, w j * f j b ∂(fairBitLaw K : Measure (Fin K → Bool))) = _
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp only [integral_const_mul]
  rfl

theorem choice_scalar_mean {k : ℕ} (w : Fin k → ℚ) (hw : ∀ j, 0 ≤ w j)
    (hm : ∑ j, w j = 1) (cap K : ℕ) (f : Fin k → (Fin K → Bool) → ℝ) :
    let R := cap * UniformNatRejection.width (denominator w)
    (fairBitKernel (R + K)).mean (fun fresh =>
      match GeneralPaperEqualCategoricalSelector.run w hw hm cap (firstBitBlock R K fresh) with
      | none => 0
      | some slot => f slot (secondBitBlock R K fresh)) =
      (1 - rejectionFailure (UniformNatRejection.acceptance (denominator w) : ℝ) cap) *
        ∑ slot, (w slot : ℝ) * (fairBitKernel K).mean (f slot) := by
  dsimp only
  let R := cap * UniformNatRejection.width (denominator w)
  rw [fairBitKernel_blocks R K
    (fun first scalar => match GeneralPaperEqualCategoricalSelector.run w hw hm cap first with
      | none => 0 | some slot => f slot scalar)]
  rw [mean_commute R K]
  have he : ∀ scalar : Fin K → Bool,
      (fairBitKernel R).mean (fun first =>
        match GeneralPaperEqualCategoricalSelector.run w hw hm cap first with
        | none => 0 | some slot => f slot scalar) =
      (1 - rejectionFailure (UniformNatRejection.acceptance (denominator w) : ℝ) cap) *
        ∑ slot, (w slot : ℝ) * f slot scalar := by
    intro scalar
    have h := GeneralPaperEqualCategoricalSelector.run_mean w hw hm cap
      (fun result => match result with | none => 0 | some slot => f slot scalar)
    simpa only [mul_zero, add_zero] using h
  simp_rw [he]
  rw [mean_mul, mean_weighted]

theorem completed_event_mean {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (cap K : ℕ) (A : Set (Allocation n)) (hA : MeasurableSet A) :
    let R := cap * UniformNatRejection.width (denominator l.weight)
    (fairBitKernel (R + K)).mean (fun fresh =>
      match (run G l cap K fresh).output with
      | none => 0
      | some row => if (fun j => (row j : ℝ)) ∈ A then (1 : ℝ) else 0) =
      (1 - rejectionFailure (UniformNatRejection.acceptance (denominator l.weight) : ℝ) cap) *
        (target G l K : Measure (Allocation n)).real A := by
  dsimp only
  have hv : ∀ fresh : Fin (cap * UniformNatRejection.width (denominator l.weight) + K) → Bool,
      (match (run G l cap K fresh).output with
        | none => 0 | some row => if (fun j => (row j : ℝ)) ∈ A then (1 : ℝ) else 0) =
      (match GeneralPaperEqualCategoricalSelector.run l.weight l.nonnegative l.mass cap
        (firstBitBlock (cap * UniformNatRejection.width (denominator l.weight)) K fresh) with
        | none => 0 | some slot =>
          if (fun j => (emit G l K slot
            (secondBitBlock (cap * UniformNatRejection.width (denominator l.weight)) K fresh) j : ℝ)) ∈ A
          then (1 : ℝ) else 0) := by
    intro fresh
    rw [output]
    cases GeneralPaperEqualCategoricalSelector.run l.weight l.nonnegative l.mass cap
      (firstBitBlock (cap * UniformNatRejection.width (denominator l.weight)) K fresh) <;> rfl
  simp_rw [hv]
  rw [choice_scalar_mean l.weight l.nonnegative l.mass cap K
    (fun slot scalar => if (fun j => (emit G l K slot scalar j : ℝ)) ∈ A then (1 : ℝ) else 0),
    target_event G l K A hA]

theorem completed_event_tends {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (K : ℕ) (A : Set (Allocation n)) (hA : MeasurableSet A) :
    Filter.Tendsto (fun cap =>
      (fairBitKernel (cap * UniformNatRejection.width (denominator l.weight) + K)).mean (fun fresh =>
        match (run G l cap K fresh).output with
        | none => 0 | some row => if (fun j => (row j : ℝ)) ∈ A then (1 : ℝ) else 0))
      Filter.atTop (nhds ((target G l K : Measure (Allocation n)).real A)) := by
  simp_rw [completed_event_mean G l _ K A hA]
  have h := failure_tends_zero (denominator l.weight) (denominator_pos l.weight)
  simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub h).mul_const
    ((target G l K : Measure (Allocation n)).real A)

theorem expected_reads {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (cap K : ℕ) :
    (fairBitKernel (cap * UniformNatRejection.width (denominator l.weight) + K)).mean
      (fun fresh => ((run G l cap K fresh).reads : ℝ)) ≤
      2 * (UniformNatRejection.width (denominator l.weight) : ℝ) + K := by
  let R := cap * UniformNatRejection.width (denominator l.weight)
  have h := (fairBitKernel (R + K)).monotone
    (fun fresh => ((run G l cap K fresh).reads : ℝ))
    (fun fresh => ((GeneralPaperEqualRejectionReads.run (denominator l.weight) cap
      (firstBitBlock R K fresh)).reads : ℝ) + K)
    (fun fresh => by exact_mod_cast reads_le G l cap K fresh)
  have hb := fairBitKernel_blocks R K (fun first _ =>
    ((GeneralPaperEqualRejectionReads.run (denominator l.weight) cap first).reads : ℝ) + K)
  simp only [(fairBitKernel K).constant, (fairBitKernel R).add,
    (fairBitKernel R).constant] at hb
  rw [hb] at h
  have he := GeneralPaperEqualRejectionReads.expected_reads
    (denominator l.weight) cap (denominator_pos l.weight)
  dsimp only [R] at h
  linarith only [h, he]

theorem expected_reads_height {n m k s : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (h : ∀ slot, RationalHeight (l.weight slot) s) (cap K : ℕ) :
    (fairBitKernel (cap * UniformNatRejection.width (denominator l.weight) + K)).mean
      (fun fresh => ((run G l cap K fresh).reads : ℝ)) ≤ 2 * (s * k + 1 : ℕ) + K := by
  have hr := expected_reads G l cap K
  have hw : (UniformNatRejection.width (denominator l.weight) : ℝ) ≤ (s * k + 1 : ℕ) := by
    exact_mod_cast rejection_width l.weight h
  linarith only [hr, hw]

noncomputable def eventTest {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (cap K : ℕ) (A : Set (Allocation n))
    (fresh : Fin (cap * UniformNatRejection.width (denominator l.weight) + K) → Bool) : ℝ :=
  match (run G l cap K fresh).output with
  | none => 0
  | some row => if (fun j => (row j : ℝ)) ∈ A then 1 else 0

theorem independent_event_mean {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (cap K : ℕ)
    (A B : Set (Allocation n)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    let D := cap * UniformNatRejection.width (denominator l.weight) + K
    (fairBitKernel (D + D)).mean (fun fresh =>
      eventTest G l cap K A (firstBitBlock D D fresh) *
        eventTest G l cap K B (secondBitBlock D D fresh)) =
      ((1 - rejectionFailure (UniformNatRejection.acceptance (denominator l.weight) : ℝ) cap) *
        (target G l K : Measure (Allocation n)).real A) *
      ((1 - rejectionFailure (UniformNatRejection.acceptance (denominator l.weight) : ℝ) cap) *
        (target G l K : Measure (Allocation n)).real B) := by
  dsimp only
  let D := cap * UniformNatRejection.width (denominator l.weight) + K
  rw [fairBitKernel_blocks D D (fun a b => eventTest G l cap K A a * eventTest G l cap K B b)]
  simp_rw [mean_mul]
  have hm : (fairBitKernel D).mean (fun a => eventTest G l cap K A a *
      (fairBitKernel D).mean (eventTest G l cap K B)) =
      (fairBitKernel D).mean (eventTest G l cap K A) *
        (fairBitKernel D).mean (eventTest G l cap K B) := by
    simpa only [mul_comm] using mean_mul D ((fairBitKernel D).mean (eventTest G l cap K B))
      (eventTest G l cap K A)
  rw [hm]
  exact congrArg₂ (fun a b : ℝ => a * b)
    (completed_event_mean G l cap K A hA) (completed_event_mean G l cap K B hB)

theorem independent_event_tends {n m k : ℕ} (G : RationalProportionalGroups n m)
    (l : RationalSegmentLottery m k) (K : ℕ)
    (A B : Set (Allocation n)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Filter.Tendsto (fun cap =>
      let D := cap * UniformNatRejection.width (denominator l.weight) + K
      (fairBitKernel (D + D)).mean (fun fresh =>
        eventTest G l cap K A (firstBitBlock D D fresh) *
          eventTest G l cap K B (secondBitBlock D D fresh)))
      Filter.atTop (nhds ((target G l K : Measure (Allocation n)).real A *
        (target G l K : Measure (Allocation n)).real B)) := by
  simp_rw [independent_event_mean G l _ K A B hA hB]
  have h := failure_tends_zero (denominator l.weight) (denominator_pos l.weight)
  have hs := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  simpa using (hs.mul_const ((target G l K : Measure (Allocation n)).real A)).mul
    (hs.mul_const ((target G l K : Measure (Allocation n)).real B))

end Blotto.GeneralPaperEqualRejectionAllocation
