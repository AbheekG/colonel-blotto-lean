import Blotto.GeneralPaperEqualNativeCache

/-! Exact uncapped execution law of the cached, original-unit output routine.
Rejection uses the stored denominator and selection uses the stored integer
counts. The normalized terminal trace measure is derived from fair words;
invalid traces have zero mass, rather than invoking an algorithmic fallback. -/
namespace Blotto.GeneralPaperEqualCachedTraceLaw
open MeasureTheory Set
open scoped BigOperators Classical ENNReal
set_option autoImplicit false
set_option maxHeartbeats 700000
open GeneralPaperPositiveSegmentCompaction (compact count)
open GeneralPaperEqualPreparedCache
open GeneralPaperEqualCachedEmission (emit)
open GeneralPaperEqualRejectionTraceMeasure

def decode {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (trace : Trace p.D p.midpointBits) : Option (RationalResourceArray n) :=
  match attempt p (fun i => last p.D p.midpointBits trace.1 trace.2 (i.cast p.rangeBits_correct)) with
  | none => none
  | some r => some (emit p model primitive A (select p r)
      (scalar p.D p.midpointBits trace.1 trace.2)).1

noncomputable def realDecode {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (trace : Trace p.D p.midpointBits) : Allocation n :=
  match decode p model primitive A trace with
  | none => fun _ => 0
  | some row => row.realAllocation

noncomputable def target {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) : Mixed n :=
  scaleLaw (p.budget : ℝ) (G.real.splitLaw ((compact l).real.dyadicLaw p.midpointBits))

theorem target_event {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (S : Set (Allocation n)) (hS : MeasurableSet S) :
    (target p : Measure (Allocation n)).real S =
      ∑ i, ((compact l).weight i : ℝ) * (fairBitKernel p.midpointBits).mean
        (fun fresh => if (emit p model primitive A i fresh).1.realAllocation ∈ S then (1 : ℝ) else 0) := by
  change (Measure.map (scaleAllocation (p.budget : ℝ))
    (GeneralPaperEqualRejectionAllocation.target G (compact l) p.midpointBits : Measure (Allocation n))).real S = _
  rw [map_measureReal_apply (measurable_scaleAllocation _) hS,
    GeneralPaperEqualRejectionAllocation.target_event _ _ _ _ (hS.preimage (measurable_scaleAllocation _))]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply congrArg (fairBitKernel p.midpointBits).mean
  funext fresh
  rw [GeneralPaperEqualCachedEmission.emit_real]
  rw [GeneralPaperEqualRejectionAllocation.emit, G.split_real]
  rfl

theorem level_event_test {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A cap : ℕ)
    (S : Set (Allocation n)) (bits : Fin (length p.D p.midpointBits cap) → Bool) :
    test p.D p.midpointBits cap
      (fun r fresh => if (emit p model primitive A (select p r) fresh).1.realAllocation ∈ S then (1 : ℝ) else 0) bits =
      if Good p.D p.midpointBits cap bits ∧ realDecode p model primitive A ⟨cap, bits⟩ ∈ S then (1 : ℝ) else 0 := by
  unfold test Good realDecode decode
  rw [attempt_eq]
  by_cases hp : (GeneralPaperEqualRejectionReads.run p.D cap (priorBits p.D p.midpointBits cap bits)).output = none
  · simp only [hp, ite_true, true_and]
    cases UniformNatRejection.attempt p.D (last p.D p.midpointBits cap bits) <;> simp
  · simp only [hp, ite_false, false_and]

theorem part_event {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A cap : ℕ)
    (S : Set (Allocation n)) (hS : MeasurableSet S) :
    (part p.D p.midpointBits cap) {bits | realDecode p model primitive A ⟨cap, bits⟩ ∈ S} =
      ENNReal.ofReal (rejectionFailure (UniformNatRejection.acceptance p.D : ℝ) cap *
        (UniformNatRejection.acceptance p.D : ℝ) * (target p : Measure (Allocation n)).real S) := by
  have h := level_mean p.D p.midpointBits cap (denominator_positive p)
    (fun r fresh => if (emit p model primitive A (select p r) fresh).1.realAllocation ∈ S then (1 : ℝ) else 0)
  rw [cached_select_mean p (fun i => (fairBitKernel p.midpointBits).mean
    (fun fresh => if (emit p model primitive A i fresh).1.realAllocation ∈ S then (1 : ℝ) else 0))] at h
  rw [← target_event p model primitive A S hS] at h
  have ht : test p.D p.midpointBits cap
      (fun r fresh => if (emit p model primitive A (select p r) fresh).1.realAllocation ∈ S then (1 : ℝ) else 0) =
      fun bits => if bits ∈ {bits | realDecode p model primitive A ⟨cap, bits⟩ ∈ S} ∩
        {bits | Good p.D p.midpointBits cap bits} then (1 : ℝ) else 0 := by
    funext bits
    rw [level_event_test]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_comm]
  rw [ht] at h
  have hf := GeneralPaperEqualRejectionAllocation.fair_event (length p.D p.midpointBits cap)
    ({bits | realDecode p model primitive A ⟨cap, bits⟩ ∈ S} ∩ {bits | Good p.D p.midpointBits cap bits})
  have hReal : (fairBitLaw (length p.D p.midpointBits cap) : Measure (Fin (length p.D p.midpointBits cap) → Bool)).real
      ({bits | realDecode p model primitive A ⟨cap, bits⟩ ∈ S} ∩ {bits | Good p.D p.midpointBits cap bits}) =
      rejectionFailure (UniformNatRejection.acceptance p.D : ℝ) cap *
        (UniformNatRejection.acceptance p.D : ℝ) * (target p : Measure (Allocation n)).real S := by
    rw [hf]
    convert h using 1
    apply congrArg (fairBitKernel (length p.D p.midpointBits cap)).mean
    funext bits
    split_ifs <;> rfl
  unfold part
  rw [Measure.restrict_apply (Set.toFinite _).measurableSet, ← hReal]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

noncomputable def outputLaw {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ) : Mixed n :=
  (law p.D p.midpointBits (denominator_positive p)).map (realDecode p model primitive A)

theorem outputLaw_eq {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ) : outputLaw p model primitive A = target p := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro S hS
  change (Measure.map (realDecode p model primitive A)
    (GeneralPaperEqualRejectionTraceMeasure.measure p.D p.midpointBits)) S = (target p : Measure (Allocation n)) S
  rw [Measure.map_apply (measurable_of_countable _) hS, GeneralPaperEqualRejectionTraceMeasure.measure,
    Measure.sum_apply _ (hS.preimage (measurable_of_countable _))]
  simp_rw [Measure.map_apply (measurable_of_countable _) (hS.preimage (measurable_of_countable _))]
  change (∑' cap, part p.D p.midpointBits cap {bits | realDecode p model primitive A ⟨cap, bits⟩ ∈ S}) = _
  simp_rw [part_event p model primitive A _ S hS]
  have hs := (success_mass_hasSum p.D (denominator_positive p)).mul_right ((target p : Measure (Allocation n)).real S)
  have ha := UniformNatRejection.acceptance_bounds p.D (denominator_positive p)
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun cap => mul_nonneg (mul_nonneg
      (rejectionFailure_unit (by linarith only [ha.1]) ha.2 cap).1 (by linarith only [ha.1]))
      measureReal_nonneg) hs.summable, hs.tsum_eq, one_mul]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem outputLaw_source {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ) :
    outputLaw p model primitive A = scaleLaw (p.budget : ℝ) (G.real.splitLaw (l.real.dyadicLaw p.midpointBits)) := by
  rw [outputLaw_eq, target, GeneralPaperPositiveSegmentCompaction.compact_dyadic_law]

theorem completed_fullBudget {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ) (hB : 0 ≤ p.budget)
    (h : ∀ i, FullBudget 1 (l.real.P i) ∧ FullBudget 1 (l.real.Q i))
    (trace : Trace p.D p.midpointBits) (row : RationalResourceArray n)
    (hr : decode p model primitive A trace = some row) : FullBudget (p.budget : ℝ) row.realAllocation := by
  unfold decode at hr
  rw [attempt_eq] at hr
  cases he : UniformNatRejection.attempt p.D (last p.D p.midpointBits trace.1 trace.2) with
  | none => simp only [he, reduceCtorEq] at hr
  | some r =>
    simp only [he, Option.some.injEq] at hr
    rw [← hr]
    exact GeneralPaperEqualCachedEmission.emit_fullBudget p model primitive A hB h _ _

theorem independent_traces {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ) :
    let μ := (law p.D p.midpointBits (denominator_positive p) : Measure (Trace p.D p.midpointBits))
    let f := realDecode p model primitive A
    Measure.map (Prod.map f f) (μ.prod μ) =
      (outputLaw p model primitive A : Measure (Allocation n)).prod
        (outputLaw p model primitive A : Measure (Allocation n)) := by
  dsimp only
  exact (Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _)).symm

theorem native_epsilon {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W
      (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1)
    (budget : ℚ) (hB : 0 < budget) (primitive : ℕ → ℕ) (A : ℕ) :
    let p := GeneralPaperEqualNativeCache.prepare bits model W
      (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget
    let μ := outputLaw p model primitive A
    Supported (budget : ℝ) μ ∧ regret v.values (budget : ℝ) μ μ ≤ (eps : ℝ) := by
  dsimp only
  rw [outputLaw_source]
  change Supported (budget : ℝ)
    (scaleLaw (budget : ℝ) (GeneralPaperEqualFiniteKernel.law
      (GeneralPaperEqualNativeSampler.rounded bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv)
      small (GeneralPaperDyadicAccuracy.prepare eps).exponent)) ∧
    regret v.values (budget : ℝ)
      (scaleLaw (budget : ℝ) (GeneralPaperEqualFiniteKernel.law
        (GeneralPaperEqualNativeSampler.rounded bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv)
        small (GeneralPaperDyadicAccuracy.prepare eps).exponent))
      (scaleLaw (budget : ℝ) (GeneralPaperEqualFiniteKernel.law
        (GeneralPaperEqualNativeSampler.rounded bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv)
        small (GeneralPaperDyadicAccuracy.prepare eps).exponent)) ≤ (eps : ℝ)
  have h := GeneralPaperEqualNativeSampler.accuracy_regret bits model W values v hv eps hp hOne small
  have hBr : (0 : ℝ) < (budget : ℝ) := by exact_mod_cast hB
  constructor
  · simpa only [mul_one] using scaleLaw_supported hBr.le _ h.1
  · have hs := regret_scale v.values hBr 1
      (GeneralPaperEqualFiniteKernel.law
        (GeneralPaperEqualNativeSampler.rounded bits model W
          (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv) small
        (GeneralPaperDyadicAccuracy.prepare eps).exponent)
      (GeneralPaperEqualFiniteKernel.law
        (GeneralPaperEqualNativeSampler.rounded bits model W
          (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv) small
        (GeneralPaperDyadicAccuracy.prepare eps).exponent)
    rw [mul_one] at hs
    exact hs.le.trans h.2

theorem native_expected_reads {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1)
    (budget : ℚ) :
    let p := GeneralPaperEqualNativeCache.prepare bits model W k values v hv small budget
    (∫⁻ trace, (GeneralPaperEqualRejectionTraceReads.reads p.D p.midpointBits trace : ℝ≥0∞)
      ∂(law p.D p.midpointBits (denominator_positive p) : Measure (Trace p.D p.midpointBits))) ≤
      ENNReal.ofReal ((33554432 : ℝ) * (binaryWordWidth n + k + 10 : ℕ)) := by
  dsimp only
  let p := GeneralPaperEqualNativeCache.prepare bits model W k values v hv small budget
  have he := GeneralPaperEqualRejectionTraceReads.expected_reads_bound p.D p.midpointBits (denominator_positive p)
  apply he.trans
  apply ENNReal.ofReal_le_ofReal
  have hr := GeneralPaperEqualNativeCache.rangeBits bits model W k values v hv small budget
  change p.rangeBits ≤ 3670016 * (binaryWordWidth n + k + 10) + 1 at hr
  rw [p.rangeBits_correct] at hr
  have hr' : (UniformNatRejection.width p.D : ℝ) ≤ (3670016 * (binaryWordWidth n + k + 10) + 1 : ℕ) := by
    exact_mod_cast hr
  change 2 * (UniformNatRejection.width p.D : ℝ) + (k + 5 : ℕ) ≤ _
  push_cast at hr' ⊢
  have hn : (0 : ℝ) ≤ binaryWordWidth n := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  nlinarith only [hr', hn, hk]

end Blotto.GeneralPaperEqualCachedTraceLaw
