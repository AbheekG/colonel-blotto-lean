import Blotto.GeneralPaperStoredTrialWork

/-! Finite actual first-success work and expected work under derived fair
terminal traces. Rejection has no truncation fallback; the observation cap
bounds only reached work. Actual directory ownership supplies each trial bound. -/
namespace Blotto.GeneralPaperStoredRejectionWork
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperEqualRejectionTraceMeasure
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
variable {prepared : GeneralPaperEqualPreparedCache.Prepared G l}

def perAttempt (model : RationalCostModel) (A w r count : ℕ) : ℕ :=
  GeneralPaperStoredTrialWork.bound model A w r count + 128 * (A + 1)

theorem finite_work (model : RationalCostModel) (A B : ℕ) (installed : Installed A)
    (hTrial : ∀ state : List Bool,(GeneralPaperStoredBooleanTrial.run model A installed GeneralPaperBooleanFreshWord.nextList state).work ≤ B)
    (cap : ℕ) (tape : ℕ → List Bool) :
    (GeneralPaperStoredBooleanRejection.run model A installed cap tape).work ≤ cap * (B + 128 * (A + 1)) := by
  induction cap generalizing tape with
  | zero => simp only [GeneralPaperStoredBooleanRejection.run,Nat.zero_mul,le_rfl]
  | succ cap ih =>
    have hCurrent := hTrial (tape 0)
    have hLater := ih (GeneralPaperStoredBooleanRejection.tail tape)
    simp only [GeneralPaperStoredBooleanRejection.run]
    split <;> dsimp only
    · nlinarith only [hCurrent,Nat.zero_le (cap * (B + 128 * (A + 1)))]
    · nlinarith only [hCurrent,hLater]

theorem work (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (cache : GeneralPaperEqualBooleanCache.Cache prepared)
    (hRead : Readback model A installed (GeneralPaperBooleanRecordCursor.expected model S A cache start))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanRecordCursor.expected model S A cache start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRecordCursor.expected model S A cache start).root.reference)
    (cap : ℕ) (tape : ℕ → List Bool) :
    (GeneralPaperStoredBooleanRejection.run model A installed cap tape).work ≤
      cap * perAttempt model A prepared.rangeBits (GeneralPaperPositiveSegmentCompaction.count l) cache.rows.length :=
  finite_work model A _ installed
    (fun state => GeneralPaperStoredTrialWork.work model S A layoutStart start plan full installed ctx cache hRead hHeaders hRoot
      GeneralPaperBooleanFreshWord.nextList state) cap tape

noncomputable def observed (model : RationalCostModel) (A : ℕ) (installed : Installed A) (N K : ℕ) (trace : Trace N K) :=
  GeneralPaperStoredBooleanRejection.run model A installed (trace.1 + 1)
    (GeneralPaperStoredRejectionTrace.rawBlocks N (GeneralPaperEqualBooleanTraceCost.tapeFor N K trace))

theorem expected_work (model : RationalCostModel) (S A layoutStart start K : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (cache : GeneralPaperEqualBooleanCache.Cache prepared)
    (hRead : Readback model A installed (GeneralPaperBooleanRecordCursor.expected model S A cache start))
    (hHeaders : ∀ header ∈ (GeneralPaperBooleanRecordCursor.expected model S A cache start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperBooleanRecordCursor.expected model S A cache start).root.reference) :
    (∫⁻ trace, ((observed model A installed prepared.D K trace).work : ℝ≥0∞)
      ∂(law prepared.D K (GeneralPaperEqualPreparedCache.denominator_positive prepared) : Measure (Trace prepared.D K))) ≤
      ENNReal.ofReal ((2 * perAttempt model A prepared.rangeBits (GeneralPaperPositiveSegmentCompaction.count l) cache.rows.length : ℕ) : ℝ) := by
  let B := perAttempt model A prepared.rangeBits (GeneralPaperPositiveSegmentCompaction.count l) cache.rows.length
  have hEach (trace : Trace prepared.D K) : (observed model A installed prepared.D K trace).work ≤ (trace.1 + 1) * B :=
    work model S A layoutStart start plan full installed ctx cache hRead hHeaders hRoot _ _
  have hm := lintegral_mono (μ := (law prepared.D K (GeneralPaperEqualPreparedCache.denominator_positive prepared) : Measure (Trace prepared.D K)))
    (fun trace => (show ((observed model A installed prepared.D K trace).work : ℝ≥0∞) ≤ (((trace.1 + 1) * B : ℕ) : ℝ≥0∞) by exact_mod_cast hEach trace))
  apply hm.trans
  rw [GeneralPaperEqualBooleanTraceCost.charge_integral prepared.D K B (GeneralPaperEqualPreparedCache.denominator_positive prepared)]
  apply ENNReal.ofReal_le_ofReal
  have ha := UniformNatRejection.acceptance_bounds prepared.D (GeneralPaperEqualPreparedCache.denominator_positive prepared)
  have hp : (0 : ℝ) < UniformNatRejection.acceptance prepared.D := by linarith only [ha.1]
  apply (div_le_iff₀ hp).mpr
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  change (B : ℝ) ≤ ((2 * B : ℕ) : ℝ) * (UniformNatRejection.acceptance prepared.D : ℝ)
  push_cast
  nlinarith only [ha.1,hB]

end Blotto.GeneralPaperStoredRejectionWork
