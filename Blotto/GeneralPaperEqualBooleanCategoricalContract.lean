import Blotto.GeneralPaperEqualBooleanTraceCost

/-! Whole output-law refinement and native linear expected categorical
bit-work bound for the Boolean rejection/selection controller. Rational
midpoint/interpolation/output work is separate from this controller price. -/
namespace Blotto.GeneralPaperEqualBooleanCategoricalContract
open MeasureTheory
open scoped BigOperators Classical ENNReal
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperEqualBooleanCache (Cache)
open GeneralPaperEqualRejectionTraceMeasure
set_option autoImplicit false
set_option maxHeartbeats 700000

noncomputable def decode {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (trace : Trace p.D p.midpointBits) : Option (RationalResourceArray n) :=
  (GeneralPaperEqualBooleanTraceCost.observed c p.midpointBits trace).output.map (fun i =>
    (GeneralPaperEqualCachedEmission.emit p model primitive A i (scalar p.D p.midpointBits trace.1 trace.2)).1)

theorem decode_eq {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (trace : Trace p.D p.midpointBits) (h : Good p.D p.midpointBits trace.1 trace.2) :
    decode c model primitive A trace = GeneralPaperEqualCachedTraceLaw.decode p model primitive A trace := by
  rw [decode, GeneralPaperEqualBooleanTraceCost.observed_output c p.midpointBits trace h]
  unfold GeneralPaperEqualCachedTraceLaw.decode
  rw [GeneralPaperEqualPreparedCache.attempt_eq]
  cases UniformNatRejection.attempt p.D (last p.D p.midpointBits trace.1 trace.2) <;> rfl

noncomputable def realDecode {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (trace : Trace p.D p.midpointBits) : Allocation n :=
  match decode c model primitive A trace with
  | none => fun _ => 0
  | some row => row.realAllocation

noncomputable def outputLaw {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ) : Mixed n :=
  (law p.D p.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive p)).map (realDecode c model primitive A)

theorem outputLaw_eq {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ) :
    outputLaw c model primitive A = GeneralPaperEqualCachedTraceLaw.outputLaw p model primitive A := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.map_congr
  filter_upwards [good_ae p.D p.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive p)] with trace h
  unfold realDecode GeneralPaperEqualCachedTraceLaw.realDecode
  rw [decode_eq c model primitive A trace h]
  rfl

theorem completed_fullBudget {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ)
    (hB : 0 ≤ p.budget) (hEnds : ∀ i, FullBudget 1 (l.real.P i) ∧ FullBudget 1 (l.real.Q i))
    (trace : Trace p.D p.midpointBits) (row : RationalResourceArray n)
    (h : decode c model primitive A trace = some row) : FullBudget (p.budget : ℝ) row.realAllocation := by
  unfold decode at h
  obtain ⟨i, _, hi⟩ := Option.map_eq_some_iff.mp h
  rw [← hi]
  exact GeneralPaperEqualCachedEmission.emit_fullBudget p model primitive A hB hEnds _ _

theorem native_epsilon {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W
      (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1)
    (budget : ℚ) (hB : 0 < budget) (primitive : ℕ → ℕ) (A : ℕ) :
    let p := GeneralPaperEqualNativeCache.prepare bits model W
      (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget
    let μ := outputLaw (GeneralPaperEqualBooleanCache.prepare p) model primitive A
    Supported (budget : ℝ) μ ∧ regret v.values (budget : ℝ) μ μ ≤ (eps : ℝ) := by
  dsimp only
  rw [outputLaw_eq]
  exact GeneralPaperEqualCachedTraceLaw.native_epsilon bits model W values v hv eps hp hOne small budget hB _ _

theorem small_bound {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (h : GeneralPaperPositiveSegmentCompaction.count l ≤ 7) :
    GeneralPaperEqualBooleanTrial.bound p + 8 ≤ 512 * (p.rangeBits + 1) := by
  have hm := Nat.mul_le_mul_right (22 * (p.rangeBits + 1) + 16) h
  unfold GeneralPaperEqualBooleanTrial.bound
  nlinarith only [hm]

theorem small_expected_work {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (h : GeneralPaperPositiveSegmentCompaction.count l ≤ 7) (K : ℕ) :
    (∫⁻ trace, ((GeneralPaperEqualBooleanTraceCost.observed c K trace).work : ℝ≥0∞)
      ∂(law p.D K (GeneralPaperEqualPreparedCache.denominator_positive p) : Measure (Trace p.D K))) ≤
      ENNReal.ofReal (1024 * (p.rangeBits + 1 : ℕ)) := by
  apply (GeneralPaperEqualBooleanTraceCost.expected_work c K).trans
  apply ENNReal.ofReal_le_ofReal
  exact_mod_cast (show 2 * (GeneralPaperEqualBooleanTrial.bound p + 8) ≤ 1024 * (p.rangeBits + 1) by
    have hh := small_bound p h
    omega)

theorem native_expected_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1)
    (budget : ℚ) :
    let p := GeneralPaperEqualNativeCache.prepare bits model W k values v hv small budget
    let c := GeneralPaperEqualBooleanCache.prepare p
    (∫⁻ trace, ((GeneralPaperEqualBooleanTraceCost.observed c p.midpointBits trace).work : ℝ≥0∞)
      ∂(law p.D p.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive p) : Measure (Trace p.D p.midpointBits))) ≤
      ENNReal.ofReal ((4294967296 : ℝ) * (binaryWordWidth n + k + 10 : ℕ)) := by
  dsimp only
  let p := GeneralPaperEqualNativeCache.prepare bits model W k values v hv small budget
  have h := small_expected_work (GeneralPaperEqualBooleanCache.prepare p)
    (GeneralPaperEqualNativeCache.compact_count _ small).2 p.midpointBits
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hw := GeneralPaperEqualNativeCache.rangeBits bits model W k values v hv small budget
  change p.rangeBits ≤ 3670016 * (binaryWordWidth n + k + 10) + 1 at hw
  exact_mod_cast (show 1024 * (p.rangeBits + 1) ≤ 4294967296 * (binaryWordWidth n + k + 10) by omega)

theorem accuracy_expected_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W
      (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    let p := GeneralPaperEqualNativeCache.prepare bits model W
      (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget
    let c := GeneralPaperEqualBooleanCache.prepare p
    (∫⁻ trace, ((GeneralPaperEqualBooleanTraceCost.observed c p.midpointBits trace).work : ℝ≥0∞)
      ∂(law p.D p.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive p) : Measure (Trace p.D p.midpointBits))) ≤
      ENNReal.ofReal ((4294967296 : ℝ) * (binaryWordWidth n + binaryWordWidth ⌈eps⁻¹⌉₊ + 10 : ℕ)) := by
  dsimp only
  have hk : (GeneralPaperDyadicAccuracy.prepare eps).exponent ≤ binaryWordWidth ⌈eps⁻¹⌉₊ := by
    have h0 := GeneralPaperDyadicAccuracy.prepare_work eps
    have h1 := GeneralPaperDyadicAccuracy.prepare_work_exact eps
    omega
  apply (native_expected_work bits model W _ values v hv small budget).trans
  apply ENNReal.ofReal_le_ofReal
  gcongr

theorem independent_traces {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (primitive : ℕ → ℕ) (A : ℕ) :
    let μ := (law p.D p.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive p) : Measure (Trace p.D p.midpointBits))
    let f := realDecode c model primitive A
    Measure.map (Prod.map f f) (μ.prod μ) =
      (outputLaw c model primitive A : Measure (Allocation n)).prod
        (outputLaw c model primitive A : Measure (Allocation n)) := by
  dsimp only
  exact (Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _)).symm

theorem width_strict (N : ℕ) (hN : 0 < N) : 2 ^ UniformNatRejection.width N < 2 * N := by
  by_cases hz : UniformNatRejection.width N = 0
  · rw [hz]
    norm_num
    omega
  · have hf : ¬N ≤ 2 ^ (UniformNatRejection.width N - 1) := by
      intro h
      have hm := widthRatioPrecision_minimal N 1 (UniformNatRejection.width N - 1) hN (by decide)
        (by simpa only [one_mul] using h)
      change UniformNatRejection.width N ≤ UniformNatRejection.width N - 1 at hm
      omega
    have he : UniformNatRejection.width N - 1 + 1 = UniformNatRejection.width N := by omega
    rw [← he, pow_succ]
    omega

theorem acceptance_strict (N : ℕ) (hN : 0 < N) : (1 / 2 : ℝ) < (UniformNatRejection.acceptance N : ℝ) := by
  have hh : ((2 ^ UniformNatRejection.width N : ℕ) : ℝ) < 2 * (N : ℝ) := by exact_mod_cast width_strict N hN
  have hp : (0 : ℝ) < (2 ^ UniformNatRejection.width N : ℕ) := by positivity
  simp only [UniformNatRejection.acceptance, Rat.cast_div, Rat.cast_natCast]
  apply (lt_div_iff₀ hp).mpr
  linarith only [hh]

end Blotto.GeneralPaperEqualBooleanCategoricalContract
