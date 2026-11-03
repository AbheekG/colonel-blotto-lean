import Blotto.GeneralPaperEqualBitDrawRates

/-! Finite observations of the complete bit draw compose the actual Boolean
rejection controller with the priced midpoint/group/output producer. Completed
observations are whole original-unit rational allocations; unfinished ones
remain unfinished. Uncapped observers use the derived fair-word trace law. -/
namespace Blotto.GeneralPaperEqualFullBitDraw
open MeasureTheory
open scoped BigOperators Classical ENNReal
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperEqualBooleanCache (Cache)
open GeneralPaperEqualRejectionTraceMeasure
set_option autoImplicit false
set_option maxHeartbeats 900000

structure Result (n : ℕ) where
  output : Option (RationalResourceArray n)
  reads : ℕ
  work : ℕ

def run {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (A cap : ℕ)
    (tape : ℕ → Fin (UniformNatRejection.width p.D) → Bool) (fresh : Fin p.midpointBits → Bool) : Result n :=
  let categorical := GeneralPaperEqualBooleanRejection.run c cap tape
  match categorical.output with
  | none => ⟨none, categorical.reads, categorical.work + 16 * A + 16⟩
  | some i =>
    let produced := GeneralPaperEqualBitPostprocessing.run p model A i fresh
    ⟨some produced.1.1, categorical.reads + produced.1.2, categorical.work + produced.2 + 16 * A + 16⟩

theorem data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (A cap : ℕ)
    (tape : ℕ → Fin (UniformNatRejection.width p.D) → Bool) (fresh : Fin p.midpointBits → Bool) :
    (run c model A cap tape fresh).output = (GeneralPaperEqualBooleanRejection.run c cap tape).output.map
      (fun i => (GeneralPaperEqualCachedEmission.emit p model (fun w => w) A i fresh).1) := by
  unfold run
  dsimp only
  cases (GeneralPaperEqualBooleanRejection.run c cap tape).output <;>
    simp only [Option.map_none, Option.map_some, GeneralPaperEqualBitPostprocessing.data]

theorem work {n m k s b d : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (A cap : ℕ)
    (tape : ℕ → Fin (UniformNatRejection.width p.D) → Bool) (fresh : Fin p.midpointBits → Bool)
    (hs : 2 ≤ s) (h : l.HeightAt s) (hB : RationalHeight p.budget b)
    (hd : 2 ≤ d) (hC : ∀ j, RationalHeight (p.routes.table.read j).2 d) :
    (run c model A cap tape fresh).work ≤ (GeneralPaperEqualBooleanRejection.run c cap tape).work +
      GeneralPaperEqualBitPostprocessing.bound model A n m p.midpointBits s b d + 16 * A + 16 := by
  unfold run
  dsimp only
  cases (GeneralPaperEqualBooleanRejection.run c cap tape).output with
  | none => dsimp only; omega
  | some i =>
    have hp := GeneralPaperEqualBitPostprocessing.work p model A i fresh hs h hB hd hC
    dsimp only
    omega

noncomputable def observed {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (A : ℕ) (trace : Trace p.D p.midpointBits) : Result n :=
  run c model A (trace.1 + 1) (GeneralPaperEqualBooleanTraceCost.tapeFor p.D p.midpointBits trace)
    (scalar p.D p.midpointBits trace.1 trace.2)

theorem observed_data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (A : ℕ) (trace : Trace p.D p.midpointBits) :
    (observed c model A trace).output = GeneralPaperEqualBooleanCategoricalContract.decode c model (fun w => w) A trace := by
  rw [observed, data]
  rfl

noncomputable def realDecode {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (A : ℕ) (trace : Trace p.D p.midpointBits) : Allocation n :=
  match (observed c model A trace).output with
  | none => fun _ => 0
  | some row => row.realAllocation

noncomputable def outputLaw {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (A : ℕ) : Mixed n :=
  (law p.D p.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive p)).map (realDecode c model A)

theorem outputLaw_eq {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (A : ℕ) :
    outputLaw c model A = GeneralPaperEqualCachedTraceLaw.outputLaw p model (fun w => w) A := by
  rw [← GeneralPaperEqualBooleanCategoricalContract.outputLaw_eq c model (fun w => w) A]
  apply ProbabilityMeasure.toMeasure_injective
  apply congrArg (fun f => Measure.map f (law p.D p.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive p) :
    Measure (Trace p.D p.midpointBits)))
  funext trace
  unfold realDecode GeneralPaperEqualBooleanCategoricalContract.realDecode
  rw [observed_data]
  rfl

theorem expected_work {n m k s b d : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    {p : Prepared G l} (c : Cache p) (model : RationalCostModel) (A : ℕ)
    (hs : 2 ≤ s) (h : l.HeightAt s) (hB : RationalHeight p.budget b)
    (hd : 2 ≤ d) (hC : ∀ j, RationalHeight (p.routes.table.read j).2 d) :
    (∫⁻ trace, ((observed c model A trace).work : ℝ≥0∞)
      ∂(law p.D p.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive p) : Measure (Trace p.D p.midpointBits))) ≤
      ((2 * (GeneralPaperEqualBooleanTrial.bound p + 8) +
        GeneralPaperEqualBitPostprocessing.bound model A n m p.midpointBits s b d + 16 * A + 16 : ℕ) : ℝ≥0∞) := by
  let μ := (law p.D p.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive p) : Measure (Trace p.D p.midpointBits))
  let Z := GeneralPaperEqualBitPostprocessing.bound model A n m p.midpointBits s b d + 16 * A + 16
  have hEach (trace : Trace p.D p.midpointBits) : (observed c model A trace).work ≤
      (GeneralPaperEqualBooleanTraceCost.observed c p.midpointBits trace).work + Z := by
    have hh := work c model A (trace.1 + 1) (GeneralPaperEqualBooleanTraceCost.tapeFor p.D p.midpointBits trace)
      (scalar p.D p.midpointBits trace.1 trace.2) hs h hB hd hC
    simpa only [observed, GeneralPaperEqualBooleanTraceCost.observed, Z, Nat.add_assoc] using hh
  have hCat := GeneralPaperEqualBooleanTraceCost.expected_work c p.midpointBits
  have hReal : ENNReal.ofReal (2 * (GeneralPaperEqualBooleanTrial.bound p + 8 : ℕ)) =
      ((2 * (GeneralPaperEqualBooleanTrial.bound p + 8) : ℕ) : ℝ≥0∞) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using ENNReal.ofReal_natCast (2 * (GeneralPaperEqualBooleanTrial.bound p + 8))
  rw [hReal] at hCat
  change (∫⁻ trace, ((observed c model A trace).work : ℝ≥0∞) ∂μ) ≤ _
  calc
    _ ≤ ∫⁻ trace, (((GeneralPaperEqualBooleanTraceCost.observed c p.midpointBits trace).work + Z : ℕ) : ℝ≥0∞) ∂μ :=
      lintegral_mono (fun trace => (show ((observed c model A trace).work : ℝ≥0∞) ≤
        (((GeneralPaperEqualBooleanTraceCost.observed c p.midpointBits trace).work + Z : ℕ) : ℝ≥0∞) by
          exact_mod_cast hEach trace))
    _ = (∫⁻ trace, ((GeneralPaperEqualBooleanTraceCost.observed c p.midpointBits trace).work : ℝ≥0∞) ∂μ) + Z := by
      simp only [Nat.cast_add]
      rw [lintegral_add_left (measurable_of_countable _)]
      simp only [lintegral_const, measure_univ, mul_one]
    _ ≤ ((2 * (GeneralPaperEqualBooleanTrial.bound p + 8) : ℕ) : ℝ≥0∞) + Z := add_le_add hCat le_rfl
    _ = _ := by simp only [Z, Nat.cast_add, add_assoc]

end Blotto.GeneralPaperEqualFullBitDraw
