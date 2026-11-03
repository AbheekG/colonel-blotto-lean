import Blotto.GeneralPaperEqualFirstSelectedDescription

/-! Actual corrected selected producer followed by one measured local
closure. Preparation, original-game semantics, exact draws and compact
description all concern this same returned object. -/
namespace Blotto.GeneralPaperEqualFirstSelectedPreparation
open MeasureTheory
open scoped ENNReal
open GeneralPaperEqualFirstNativeFacts (rounded)
open GeneralPaperEqualSelectedSampler (Sampler traceLaw observed realDecode outputLaw)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def run {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) : Sampler (rounded true model W k values v hv) k budget × ℕ :=
  let source := GeneralPaperEqualFirstBitDispatch.run model W A k values v hv budget
  let closed := GeneralPaperEqualSelectedSampler.close model A k budget source.1
  (closed.1,source.2+closed.2+64*A+64)

def bound {n : ℕ} (model : RationalCostModel) (W A k : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperEqualFirstPreparationWork.bound model W A k values budget+
    GeneralPaperEqualSelectedClosureWork.price model A n k (rationalWordWidth budget)+64*A+64

theorem work {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) :
    (run model W A k values v hv budget).2 ≤ bound model W A k values budget := by
  have h0 := GeneralPaperEqualFirstPreparationWork.work model W A k values v hv budget
  have h1 := GeneralPaperEqualSelectedClosureWork.work model A k budget
    (GeneralPaperEqualFirstBitDispatch.run model W A k values v hv budget).1
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add h0 h1) (64*A)) 64

theorem branch {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) :
    (run model W A k values v hv budget).1.branch =
      (GeneralPaperEqualFirstBitDispatch.run model W A k values v hv budget).1 := rfl

theorem original_regret {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (hB : 0 < budget) :
    let a := (run model W A k values v hv budget).1
    Supported (budget : ℝ) (outputLaw model a) ∧
      regret v.values (budget : ℝ) (outputLaw model a) (outputLaw model a) ≤ 3*(1/(2 : ℝ)^k)/64 :=
  GeneralPaperEqualFirstBitDispatch.original_regret model W A k values v hv budget hB

theorem sampler_contract {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (hB : 0 ≤ budget) :
    let a := (run model W A k values v hv budget).1
    (traceLaw a).map (realDecode model a) = outputLaw model a ∧
    (∀ᵐ trace ∂(traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch)),
      ∃ row, (observed model a trace).output = some row) ∧
    (∀ trace row, (observed model a trace).output = some row →
      FullBudget (budget : ℝ) row.realAllocation ∧
        ∀ j, RationalHeight (row.allocation j) (GeneralPaperEqualBitDrawRates.word n (k+1) (rationalWordWidth budget))) ∧
    (∫⁻ trace, ((observed model a trace).reads : ℝ≥0∞)
      ∂(traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))) ≤
      (GeneralPaperEqualFirstBitSampling.readsBound n k : ℝ≥0∞) ∧
    (∫⁻ trace, ((observed model a trace).work : ℝ≥0∞)
      ∂(traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))) ≤
      (GeneralPaperEqualSelectedDraw.workBound model n (k+1) (rationalWordWidth budget) : ℝ≥0∞) ∧
    GeneralPaperEqualSelectedDescription.footprint a ≤
      2*GeneralPaperEqualDescriptionRates.paperBound n (k+1) (rationalWordWidth budget) ∧
    GeneralPaperEqualSelectedDescription.footprint a < 2^a.address := by
  let a := (run model W A k values v hv budget).1
  refine ⟨GeneralPaperEqualSelectedSampler.law model a,GeneralPaperEqualSelectedSampler.completed_ae model a,?_,
    GeneralPaperEqualFirstBitSampling.expected_reads model W a.address k values v hv budget a.branch,
    GeneralPaperEqualFirstBitWork.expected_work model W k values v hv budget a,
    GeneralPaperEqualFirstSelectedDescription.paper_bound model W k values v hv budget a,
    GeneralPaperEqualFirstSelectedDescription.capacity model W k values v hv budget a⟩
  intro trace row hRow
  exact ⟨GeneralPaperEqualSelectedSampler.completed_budget model a hB trace row hRow,
    GeneralPaperEqualFirstBitOutput.completed_height model W a.address k values v hv budget
      (rationalHeight_of_wordWidth budget) a.branch trace row hRow⟩

theorem independent_players {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) :
    let a := (run model W A k values v hv budget).1
    let μ := (traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))
    Measure.map (Prod.map (realDecode model a) (realDecode model a)) (μ.prod μ) =
      (outputLaw model a : Measure (Allocation n)).prod (outputLaw model a : Measure (Allocation n)) :=
  GeneralPaperEqualBitBranchDraw.independent_players model _ _

end Blotto.GeneralPaperEqualFirstSelectedPreparation
