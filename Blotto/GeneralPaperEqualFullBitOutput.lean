import Blotto.GeneralPaperEqualFullBitContract

/-! Completion, exact reads, hard budgets, rational output height and player
independence refer to the same complete bit-priced source sampler. -/
namespace Blotto.GeneralPaperEqualFullBitOutput
open MeasureTheory
open scoped BigOperators Classical ENNReal
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperEqualBooleanCache (Cache)
open GeneralPaperEqualRejectionTraceMeasure
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem success_stable_one {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (A cap : ℕ)
    (tape : ℕ → Fin (UniformNatRejection.width p.D) → Bool) (fresh : Fin p.midpointBits → Bool)
    (row : RationalResourceArray n) (h : (GeneralPaperEqualFullBitDraw.run c model A cap tape fresh).output = some row) :
    GeneralPaperEqualFullBitDraw.run c model A (cap + 1) tape fresh = GeneralPaperEqualFullBitDraw.run c model A cap tape fresh := by
  rw [GeneralPaperEqualFullBitDraw.data] at h
  obtain ⟨i, hi, _⟩ := Option.map_eq_some_iff.mp h
  have hs := GeneralPaperEqualBooleanRejection.success_stable_one c cap tape i hi
  unfold GeneralPaperEqualFullBitDraw.run
  rw [hs]

theorem completed_ae {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (A : ℕ) :
    ∀ᵐ trace ∂(law p.D p.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive p) : Measure (Trace p.D p.midpointBits)),
      ∃ row, (GeneralPaperEqualFullBitDraw.observed c model A trace).output = some row := by
  filter_upwards [GeneralPaperEqualBooleanTraceCost.completed_ae c p.midpointBits] with trace h
  obtain ⟨i, hi⟩ := h
  rw [GeneralPaperEqualFullBitDraw.observed_data, GeneralPaperEqualBooleanCategoricalContract.decode, hi]
  exact ⟨_, rfl⟩

theorem observed_reads {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (A : ℕ) (trace : Trace p.D p.midpointBits)
    (h : Good p.D p.midpointBits trace.1 trace.2) :
    (GeneralPaperEqualFullBitDraw.observed c model A trace).reads =
      (trace.1 + 1) * UniformNatRejection.width p.D + p.midpointBits := by
  have hReads := GeneralPaperEqualBooleanTraceCost.observed_reads c p.midpointBits trace h
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h.2
  have hOut := GeneralPaperEqualBooleanTraceCost.observed_output c p.midpointBits trace h
  rw [hr, Option.map_some] at hOut
  unfold GeneralPaperEqualFullBitDraw.observed GeneralPaperEqualFullBitDraw.run
  dsimp only
  change ((match (GeneralPaperEqualBooleanTraceCost.observed c p.midpointBits trace).output with
    | none => _ | some i => _) : GeneralPaperEqualFullBitDraw.Result n).reads = _
  rw [hOut]
  dsimp only
  rw [GeneralPaperEqualBitPostprocessing.reads]
  exact congrArg (fun x => x + p.midpointBits) hReads

theorem expected_reads_exact {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (A : ℕ) :
    (∫⁻ trace, ((GeneralPaperEqualFullBitDraw.observed c model A trace).reads : ℝ≥0∞)
      ∂(law p.D p.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive p) : Measure (Trace p.D p.midpointBits))) =
      ENNReal.ofReal ((UniformNatRejection.width p.D : ℝ) / (UniformNatRejection.acceptance p.D : ℝ) + p.midpointBits) := by
  rw [← GeneralPaperEqualRejectionTraceReads.expected_reads_exact p.D p.midpointBits
    (GeneralPaperEqualPreparedCache.denominator_positive p)]
  apply lintegral_congr_ae
  filter_upwards [good_ae p.D p.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive p)] with trace h
  rw [observed_reads c model A trace h]
  rfl

theorem completed_budget {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (A cap : ℕ)
    (tape : ℕ → Fin (UniformNatRejection.width p.D) → Bool) (fresh : Fin p.midpointBits → Bool)
    (hB : 0 ≤ p.budget) (hEnds : ∀ i, FullBudget 1 (l.real.P i) ∧ FullBudget 1 (l.real.Q i))
    (row : RationalResourceArray n) (h : (GeneralPaperEqualFullBitDraw.run c model A cap tape fresh).output = some row) :
    FullBudget (p.budget : ℝ) row.realAllocation := by
  rw [GeneralPaperEqualFullBitDraw.data] at h
  obtain ⟨i, _, hi⟩ := Option.map_eq_some_iff.mp h
  rw [← hi]
  exact GeneralPaperEqualCachedEmission.emit_fullBudget p model (fun w => w) A hB hEnds i fresh

theorem independent_traces {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (A : ℕ) :
    let μ := (law p.D p.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive p) : Measure (Trace p.D p.midpointBits))
    let f := GeneralPaperEqualFullBitDraw.realDecode c model A
    Measure.map (Prod.map f f) (μ.prod μ) =
      (GeneralPaperEqualFullBitDraw.outputLaw c model A : Measure (Allocation n)).prod
        (GeneralPaperEqualFullBitDraw.outputLaw c model A : Measure (Allocation n)) := by
  dsimp only
  exact (Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _)).symm

theorem real_bit_law {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (model : RationalCostModel) :
    GeneralPaperEqualStoredBitSampler.outputLaw sampler model = GeneralPaperEqualRealDraw.outputLaw sampler.prepared := by
  rw [GeneralPaperEqualStoredBitSampler.outputLaw, GeneralPaperEqualFullBitDraw.outputLaw_eq,
    GeneralPaperEqualCachedTraceLaw.outputLaw_eq, GeneralPaperEqualRealDraw.outputLaw_eq]

theorem native_written_output {n b : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1)
    (budget : ℚ) (hB : 0 ≤ budget) (hHeight : RationalHeight budget b)
    (cap : ℕ)
    (tape : ℕ → Fin (UniformNatRejection.width
      (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget).prepared.D) → Bool)
    (fresh : Fin (k + 5) → Bool) (row : RationalResourceArray n)
    (h : (GeneralPaperEqualStoredBitSampler.run
      (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget) model cap tape fresh).output = some row) :
    FullBudget (budget : ℝ) row.realAllocation ∧
      ∀ j, RationalHeight (row.allocation j) (33554432 * (b + binaryWordWidth n + k + 10)) := by
  unfold GeneralPaperEqualStoredBitSampler.run at h
  have hd := GeneralPaperEqualFullBitDraw.data
    (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget).categorical model
    (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget).address cap tape fresh
  rw [hd] at h
  obtain ⟨i, _, hi⟩ := Option.map_eq_some_iff.mp h
  rw [← hi]
  exact ⟨GeneralPaperEqualNativeCache.output_fullBudget bits model W k values v hv small budget hB _ _ i fresh,
    GeneralPaperEqualNativeCache.output_height bits model W k values v hv small budget hHeight _ _ i fresh⟩

end Blotto.GeneralPaperEqualFullBitOutput
