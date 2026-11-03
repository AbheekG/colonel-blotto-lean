import Blotto.GeneralPaperEqualFirstRealContract

/-! Exact whole-player laws and logarithmic expected fair bits for the
same actual c=256 bit return. The categorical trials keep their checked
success probability at least one half; midpoint precision is k+5. -/
namespace Blotto.GeneralPaperEqualFirstBitSampling
open MeasureTheory
open scoped ENNReal
open GeneralPaperEqualFirstRounding
open GeneralPaperEqualBitBranch (Prepared outputLaw)
open GeneralPaperEqualBitBranchDraw (Trace traceLaw observed realDecode)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def readsBound (n k : ℕ) : ℕ := 8388608*(binaryWordWidth n+k+11)

theorem expected_reads {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (p : Prepared (rounded true model W k values v hv) k budget) :
    (∫⁻ trace, ((observed model A p trace).reads : ℝ≥0∞) ∂(traceLaw p : Measure (Trace p))) ≤
      (readsBound n k : ℝ≥0∞) := by
  cases p with
  | dominant chosen heavy row correct =>
    simp only [observed, Nat.cast_zero, lintegral_zero, zero_le]
  | grouped small sampler hK hB =>
    let p := sampler.prepared
    change (∫⁻ trace, ((GeneralPaperEqualFullBitDraw.observed sampler.categorical model sampler.address trace).reads : ℝ≥0∞)
      ∂(GeneralPaperEqualRejectionTraceMeasure.law p.D p.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive p) :
          Measure (GeneralPaperEqualRejectionTraceMeasure.Trace p.D p.midpointBits))) ≤ _
    rw [GeneralPaperEqualFullBitOutput.expected_reads_exact]
    have h := GeneralPaperEqualRejectionTraceReads.expected_reads_bound p.D p.midpointBits
      (GeneralPaperEqualPreparedCache.denominator_positive p)
    rw [GeneralPaperEqualRejectionTraceReads.expected_reads_exact] at h
    apply h.trans
    have hw := GeneralPaperEqualFirstHeights.rejection_range true model W k values v hv small p
    have hk : p.midpointBits = k+5 := sampler.exponent_correct.trans (congrArg (fun k => k+5) hK)
    have he : p.rangeBits = UniformNatRejection.width p.D := p.rangeBits_correct
    have hn : 2*UniformNatRejection.width p.D+p.midpointBits ≤ readsBound n k := by
      unfold readsBound
      omega
    have hr : 2*(UniformNatRejection.width p.D : ℝ)+p.midpointBits ≤ (readsBound n k : ℝ) := by exact_mod_cast hn
    exact (ENNReal.ofReal_le_ofReal hr).trans_eq (by simp)

def TrialsAtLeastHalf {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} : Prepared v k budget → Prop
  | .dominant _ _ _ _ => True
  | .grouped _ sampler _ _ => (1/2 : ℝ) ≤ (UniformNatRejection.acceptance sampler.prepared.D : ℝ)

theorem trials_at_least_half {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (p : Prepared v k budget) : TrialsAtLeastHalf p := by
  cases p with
  | dominant _ _ _ _ => trivial
  | grouped _ sampler _ _ =>
    exact (UniformNatRejection.acceptance_bounds sampler.prepared.D
      (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared)).1

theorem same_return {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (hB : 0 < budget) :
    let p := (GeneralPaperEqualFirstBitDispatch.run model W A k values v hv budget).1
    Supported (budget : ℝ) (outputLaw model p) ∧
    regret v.values (budget : ℝ) (outputLaw model p) (outputLaw model p) ≤ 3*(1/(2 : ℝ)^k)/64 ∧
    (traceLaw p).map (realDecode model A p) = outputLaw model p ∧
    (∀ trace row, (observed model A p trace).output = some row → FullBudget (budget : ℝ) row.realAllocation) ∧
    (∫⁻ trace, ((observed model A p trace).reads : ℝ≥0∞) ∂(traceLaw p : Measure (Trace p))) ≤
      (readsBound n k : ℝ≥0∞) ∧ TrialsAtLeastHalf p ∧
    (∀ᵐ trace ∂(traceLaw p : Measure (Trace p)), ∃ row, (observed model A p trace).output = some row) := by
  have h := GeneralPaperEqualFirstBitDispatch.original_regret model W A k values v hv budget hB
  exact ⟨h.1, h.2, GeneralPaperEqualBitBranchDraw.law model A _,
    fun trace row hRow => GeneralPaperEqualBitBranchDraw.completed_budget model A _ (by exact_mod_cast hB.le) trace row hRow,
    expected_reads model W A k values v hv budget _, trials_at_least_half _,
    GeneralPaperEqualBitBranchDraw.completed_ae model A _⟩

theorem independent_players {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) :
    let p := (GeneralPaperEqualFirstBitDispatch.run model W A k values v hv budget).1
    let μ := (traceLaw p : Measure (Trace p))
    Measure.map (Prod.map (realDecode model A p) (realDecode model A p)) (μ.prod μ) =
      (outputLaw model p : Measure (Allocation n)).prod (outputLaw model p : Measure (Allocation n)) :=
  GeneralPaperEqualBitBranchDraw.independent_players model A _

end Blotto.GeneralPaperEqualFirstBitSampling
