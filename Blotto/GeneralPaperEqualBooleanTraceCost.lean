import Blotto.GeneralPaperEqualBooleanRejection

/-! The actual Boolean controller observed on the already normalized fair-
word terminal trace measure. Realization is proof-only reconstruction of the
source tape from a finite execution word, never a sampler or cost oracle. -/
namespace Blotto.GeneralPaperEqualBooleanTraceCost
open MeasureTheory
open scoped BigOperators Classical ENNReal
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperEqualBooleanCache (Cache)
open GeneralPaperEqualRejectionTraceMeasure
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem code_prior (N K cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width N) → Bool)
    (midpoint : Fin K → Bool) :
    priorBits N K cap (codeWord N K cap tape midpoint) = GeneralPaperEqualRejectionPrefix.seed (UniformNatRejection.width N) cap tape := by
  funext j
  exact Fin.append_left _ _ j

theorem code_last (N K cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width N) → Bool)
    (midpoint : Fin K → Bool) : last N K cap (codeWord N K cap tape midpoint) = tape cap := by
  funext j
  change Fin.append _ (Fin.append (tape cap) midpoint) ((j.castAdd K).natAdd (cap * UniformNatRejection.width N)) = _
  rw [Fin.append_right, Fin.append_left]

theorem code_output (N K cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width N) → Bool)
    (bits : Fin (length N K cap) → Bool) (hCode : codeWord N K cap tape (scalar N K cap bits) = bits)
    (hGood : Good N K cap bits) :
    (GeneralPaperEqualRejectionPrefix.blockRun N (cap + 1) tape).output = UniformNatRejection.attempt N (last N K cap bits) := by
  have hs : GeneralPaperEqualRejectionPrefix.seed (UniformNatRejection.width N) cap tape = priorBits N K cap bits := by
    rw [← hCode, code_prior]
  have hl : tape cap = last N K cap bits := by rw [← hCode, code_last]
  have hf : (GeneralPaperEqualRejectionPrefix.blockRun N cap tape).output = none := by
    rw [← GeneralPaperEqualRejectionPrefix.run_seed, hs]
    exact hGood.1
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hGood.2
  have he := GeneralPaperEqualRejectionPrefix.first_success N cap tape r
    ((GeneralPaperEqualRejectionPrefix.failure_all N cap tape).mp hf) (by rw [hl]; exact hr)
  rw [he, hr]

noncomputable def tapeFor (N K : ℕ) (trace : Trace N K) : ℕ → Fin (UniformNatRejection.width N) → Bool :=
  if h : Good N K trace.1 trace.2 then Classical.choose (good_realization N K trace.1 trace.2 h)
  else fun _ _ => false

theorem tapeFor_code (N K : ℕ) (trace : Trace N K) (h : Good N K trace.1 trace.2) :
    codeWord N K trace.1 (tapeFor N K trace) (scalar N K trace.1 trace.2) = trace.2 := by
  rw [tapeFor, dite_eq_left h]
  exact (Classical.choose_spec (Classical.choose_spec (good_realization N K trace.1 trace.2 h))).1

noncomputable def observed {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (K : ℕ) (trace : Trace p.D K) :=
  GeneralPaperEqualBooleanRejection.run c (trace.1 + 1) (tapeFor p.D K trace)

theorem observed_output {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (K : ℕ) (trace : Trace p.D K) (h : Good p.D K trace.1 trace.2) :
    (observed c K trace).output = (UniformNatRejection.attempt p.D (last p.D K trace.1 trace.2)).map
      (GeneralPaperEqualPreparedCache.select p) := by
  rw [observed, (GeneralPaperEqualBooleanRejection.data c _ _).1,
    code_output p.D K trace.1 _ trace.2 (tapeFor_code p.D K trace h) h]

theorem observed_work {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (K : ℕ) (trace : Trace p.D K) :
    (observed c K trace).work ≤ (trace.1 + 1) * (GeneralPaperEqualBooleanTrial.bound p + 8) :=
  GeneralPaperEqualBooleanRejection.work c _ _

theorem charge_hasSum (N B : ℕ) (hN : 0 < N) :
    HasSum (fun cap : ℕ => (((cap + 1) * B : ℕ) : ℝ) *
      (rejectionFailure (UniformNatRejection.acceptance N : ℝ) cap * (UniformNatRejection.acceptance N : ℝ)))
      ((B : ℝ) / (UniformNatRejection.acceptance N : ℝ)) := by
  have h := (GeneralPaperEqualRejectionTraceReads.attempts_hasSum N hN).mul_left (B : ℝ)
  convert h using 1
  · funext cap
    push_cast
    ring
  · ring

theorem charge_integral (N K B : ℕ) (hN : 0 < N) :
    (∫⁻ trace, (((trace.1 + 1) * B : ℕ) : ℝ≥0∞) ∂(law N K hN : Measure (Trace N K))) =
      ENNReal.ofReal ((B : ℝ) / (UniformNatRejection.acceptance N : ℝ)) := by
  have ha := UniformNatRejection.acceptance_bounds N hN
  have hs := charge_hasSum N B hN
  change (∫⁻ trace : Trace N K, (((trace.1 + 1) * B : ℕ) : ℝ≥0∞)
    ∂GeneralPaperEqualRejectionTraceMeasure.measure N K) = _
  calc
    _ = ∑' cap, (((cap + 1) * B : ℕ) : ℝ≥0∞) * part N K cap Set.univ := by
      rw [GeneralPaperEqualRejectionTraceMeasure.measure, lintegral_sum_measure]
      apply tsum_congr
      intro cap
      rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
      change (∫⁻ _bits, (((cap + 1) * B : ℕ) : ℝ≥0∞) ∂part N K cap) = _
      exact lintegral_const _
    _ = ∑' cap, ENNReal.ofReal ((((cap + 1) * B : ℕ) : ℝ) *
        (rejectionFailure (UniformNatRejection.acceptance N : ℝ) cap * (UniformNatRejection.acceptance N : ℝ))) := by
      apply tsum_congr
      intro cap
      rw [part_mass N K cap hN]
      have hn : ENNReal.ofReal ((((cap + 1) * B : ℕ) : ℝ)) = (((cap + 1) * B : ℕ) : ℝ≥0∞) := ENNReal.ofReal_natCast _
      rw [← hn, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun cap => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
          (rejectionFailure_unit (by linarith only [ha.1]) ha.2 cap).1 (by linarith only [ha.1])))
        hs.summable, hs.tsum_eq]

theorem expected_work {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (K : ℕ) :
    (∫⁻ trace, ((observed c K trace).work : ℝ≥0∞)
      ∂(law p.D K (GeneralPaperEqualPreparedCache.denominator_positive p) : Measure (Trace p.D K))) ≤
      ENNReal.ofReal (2 * (GeneralPaperEqualBooleanTrial.bound p + 8 : ℕ)) := by
  have hm := lintegral_mono (μ := (law p.D K (GeneralPaperEqualPreparedCache.denominator_positive p) : Measure (Trace p.D K)))
    (fun trace => (show ((observed c K trace).work : ℝ≥0∞) ≤ (((trace.1 + 1) * (GeneralPaperEqualBooleanTrial.bound p + 8) : ℕ) : ℝ≥0∞) by
      exact_mod_cast observed_work c K trace))
  apply hm.trans
  rw [charge_integral p.D K _ (GeneralPaperEqualPreparedCache.denominator_positive p)]
  apply ENNReal.ofReal_le_ofReal
  have ha := UniformNatRejection.acceptance_bounds p.D (GeneralPaperEqualPreparedCache.denominator_positive p)
  have hp : (0 : ℝ) < UniformNatRejection.acceptance p.D := by linarith only [ha.1]
  apply (div_le_iff₀ hp).mpr
  have hB : (0 : ℝ) ≤ (GeneralPaperEqualBooleanTrial.bound p + 8 : ℕ) := Nat.cast_nonneg _
  nlinarith only [ha.1, hB]

theorem observed_reads {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (K : ℕ) (trace : Trace p.D K) (h : Good p.D K trace.1 trace.2) :
    (observed c K trace).reads = (trace.1 + 1) * UniformNatRejection.width p.D := by
  have hs := Classical.choose_spec (good_realization p.D K trace.1 trace.2 h)
  have hr : ∃ r, GeneralPaperEqualRejectionPrefix.blockRun p.D (trace.1 + 1) (tapeFor p.D K trace) =
      ⟨some r, (trace.1 + 1) * UniformNatRejection.width p.D⟩ := by
    rw [tapeFor, dite_eq_left h]
    exact ⟨Classical.choose hs, (Classical.choose_spec hs).2⟩
  obtain ⟨r, hr⟩ := hr
  rw [observed, (GeneralPaperEqualBooleanRejection.data c _ _).2, hr]

theorem completed_ae {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (K : ℕ) :
    ∀ᵐ trace ∂(law p.D K (GeneralPaperEqualPreparedCache.denominator_positive p) : Measure (Trace p.D K)),
      ∃ i, (observed c K trace).output = some i := by
  filter_upwards [good_ae p.D K (GeneralPaperEqualPreparedCache.denominator_positive p)] with trace h
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h.2
  rw [observed_output c K trace h, hr]
  exact ⟨_, rfl⟩

theorem expected_reads_exact {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (K : ℕ) :
    (∫⁻ trace, ((observed c K trace).reads : ℝ≥0∞)
      ∂(law p.D K (GeneralPaperEqualPreparedCache.denominator_positive p) : Measure (Trace p.D K))) =
      ENNReal.ofReal ((UniformNatRejection.width p.D : ℝ) / (UniformNatRejection.acceptance p.D : ℝ)) := by
  calc
    _ = ∫⁻ trace, (((trace.1 + 1) * UniformNatRejection.width p.D : ℕ) : ℝ≥0∞)
        ∂(law p.D K (GeneralPaperEqualPreparedCache.denominator_positive p) : Measure (Trace p.D K)) := by
      apply lintegral_congr_ae
      filter_upwards [good_ae p.D K (GeneralPaperEqualPreparedCache.denominator_positive p)] with trace h
      rw [observed_reads c K trace h]
    _ = _ := charge_integral p.D K _ (GeneralPaperEqualPreparedCache.denominator_positive p)

end Blotto.GeneralPaperEqualBooleanTraceCost
