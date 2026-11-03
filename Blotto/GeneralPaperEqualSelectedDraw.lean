import Blotto.GeneralPaperEqualSelectedSampler

/-! Same-return expected bit work, random reads and written-coordinate
height. Original budget precision enters draw work through the original-unit
output; input accuracy encoding does not occur in these bounds. -/
namespace Blotto.GeneralPaperEqualSelectedDraw
open MeasureTheory
open GeneralPaperEqualSelectedSampler
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

theorem copy_allocation {n : ℕ} (A : ℕ) (row : RationalResourceArray n) (j : Fin n) :
    (GeneralPaperEqualBitBranchDraw.copyRow A row).1.allocation j = row.allocation j := by
  change (PaperIndexedArrayConstruction.run id A
    (fun j : Fin n => (row.allocation j, rationalWordWidth (row.allocation j) + 32 * A + 32))).1.read j = _
  rw [PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn]

theorem pure_copy_work {n : ℕ} (A : ℕ) (budget : ℚ) (chosen : Fin n) (row : RationalResourceArray n)
    (h : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen) :
    (GeneralPaperEqualBitBranchDraw.copyRow A row).2 ≤ GeneralPaperEqualBitVertex.bound A n (rationalWordWidth budget) := by
  have he : (fun j : Fin n => (row.allocation j, rationalWordWidth (row.allocation j) + 32 * A + 32)) =
      (fun j : Fin n => let q := if j = chosen then budget else 0; (q, rationalWordWidth q + 32 * A + 32)) := by
    funext j
    rw [GeneralPaperEqualBitCanonical.pure_coordinates budget chosen row h j]
  unfold GeneralPaperEqualBitBranchDraw.copyRow
  dsimp only
  rw [he]
  exact GeneralPaperEqualBitVertex.work A budget chosen

def pureBound (n k b : ℕ) : ℕ :=
  let A := 2 * GeneralPaperEqualBitDrawRates.log n k b + 1
  b + 3 * n + n * (32 * A + 32) +
    (n + 1) * (6 * A + 10 * binaryWordWidth (n + 1) + 28) + 64 * A + 64

theorem pure_work_bound {n : ℕ} (A k : ℕ) (budget : ℚ) (chosen : Fin n) (row : RationalResourceArray n)
    (h : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hA : A ≤ 2 * GeneralPaperEqualBitDrawRates.log n k (rationalWordWidth budget) + 1) :
    (GeneralPaperEqualBitBranchDraw.copyRow A row).2 ≤ pureBound n k (rationalWordWidth budget) := by
  have hp := pure_copy_work A budget chosen row h
  have ho := PaperIndexedArrayConstruction.overhead_bound id 1 (fun w => by change w ≤ 1 * w; omega) A n n le_rfl
  simp only [Nat.mul_one] at ho
  apply hp.trans
  unfold GeneralPaperEqualBitVertex.bound pureBound
  dsimp only
  calc
    _ ≤ rationalWordWidth budget + 3 * n + n * (32 * A + 32) +
        (n + 1) * (6 * A + 10 * binaryWordWidth (n + 1) + 28) + 64 * A + 64 := by omega
    _ ≤ _ := by gcongr

def workBound (model : RationalCostModel) (n k b : ℕ) : ℕ :=
  GeneralPaperEqualFullBitContract.bound model n k b + pureBound n k b

theorem expected_work {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    (∫⁻ trace, ((observed model a trace).work : ℝ≥0∞) ∂(traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))) ≤
      (workBound model n k (rationalWordWidth budget) : ℝ≥0∞) := by
  have hA := address_bound a
  cases a with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      have hp := pure_work_bound A k budget chosen row correct hA
      have hn : (GeneralPaperEqualBitBranchDraw.copyRow A row).2 ≤ workBound model n k (rationalWordWidth budget) :=
        hp.trans (Nat.le_add_left _ _)
      have he : ((GeneralPaperEqualBitBranchDraw.copyRow A row).2 : ℝ≥0∞) ≤
          (workBound model n k (rationalWordWidth budget) : ℝ≥0∞) := by exact_mod_cast hn
      simp only [observed, traceLaw, GeneralPaperEqualBitBranchDraw.observed,
        GeneralPaperEqualBitBranchDraw.traceLaw, lintegral_const]
      change ((GeneralPaperEqualBitBranchDraw.copyRow A row).2 : ℝ≥0∞) *
        (GeneralPaperEqualBitBranchDraw.unitLaw : Measure Unit) Set.univ ≤ _
      rw [measure_univ, mul_one]
      exact he
    | grouped small sampler hK hB =>
      have hs := GeneralPaperEqualBitCanonical.sampler_canonical sampler k budget hK hB
      subst sampler
      have h := GeneralPaperEqualFullBitContract.native_expected_work true model W k values v hv small budget
      exact h.trans (by exact_mod_cast (Nat.le_add_right
        (GeneralPaperEqualFullBitContract.bound model n k (rationalWordWidth budget)) (pureBound n k (rationalWordWidth budget))))

def readsBound (n k : ℕ) : ℕ := 8388608 * (binaryWordWidth n + k + 10)

theorem expected_reads {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    (∫⁻ trace, ((observed model a trace).reads : ℝ≥0∞) ∂(traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))) ≤
      (readsBound n k : ℝ≥0∞) := by
  cases a with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      simp only [observed, traceLaw, GeneralPaperEqualBitBranchDraw.observed,
        Nat.cast_zero, lintegral_zero, zero_le]
    | grouped small sampler hK hB =>
      have hs := GeneralPaperEqualBitCanonical.sampler_canonical sampler k budget hK hB
      subst sampler
      let s := GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget
      let p := s.prepared
      change (∫⁻ trace, ((GeneralPaperEqualFullBitDraw.observed s.categorical model s.address trace).reads : ℝ≥0∞) ∂
        (GeneralPaperEqualRejectionTraceMeasure.law p.D p.midpointBits
          (GeneralPaperEqualPreparedCache.denominator_positive p) :
            Measure (GeneralPaperEqualRejectionTraceMeasure.Trace p.D p.midpointBits))) ≤ _
      rw [GeneralPaperEqualFullBitOutput.expected_reads_exact]
      have h := GeneralPaperEqualRejectionTraceReads.expected_reads_bound p.D p.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive p)
      rw [GeneralPaperEqualRejectionTraceReads.expected_reads_exact] at h
      apply h.trans
      have hw := GeneralPaperEqualNativeCache.rangeBits true model W k values v hv small budget
      have hk : p.midpointBits = k + 5 := rfl
      have he : p.rangeBits = UniformNatRejection.width p.D := p.rangeBits_correct
      have hn : 2 * UniformNatRejection.width p.D + p.midpointBits ≤ readsBound n k := by
        dsimp only [readsBound] at *
        change p.rangeBits ≤ 3670016 * (binaryWordWidth n + k + 10) + 1 at hw
        omega
      have hr : 2 * (UniformNatRejection.width p.D : ℝ) + p.midpointBits ≤ (readsBound n k : ℝ) := by exact_mod_cast hn
      exact (ENNReal.ofReal_le_ofReal hr).trans_eq (by simp)

theorem written_output {n b : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (hB : 0 ≤ budget) (hHeight : RationalHeight budget b)
    (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (trace : GeneralPaperEqualBitBranchDraw.Trace a.branch) (row : RationalResourceArray n)
    (h : (observed model a trace).output = some row) :
    FullBudget (budget : ℝ) row.realAllocation ∧
      ∀ j, RationalHeight (row.allocation j) (33554432 * (b + binaryWordWidth n + k + 10)) := by
  refine ⟨completed_budget model a hB trace row h, ?_⟩
  cases a with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy stored correct =>
      have he : (GeneralPaperEqualBitBranchDraw.copyRow A stored).1 = row := Option.some.inj h
      rw [← he]
      intro j
      rw [copy_allocation, GeneralPaperEqualBitCanonical.pure_coordinates budget chosen stored correct j]
      split_ifs
      · exact hHeight.mono (by omega)
      · exact (show RationalHeight (0 : ℚ) 1 by norm_num [RationalHeight]).mono (by omega)
    | grouped small sampler hK hBudget =>
      have hs := GeneralPaperEqualBitCanonical.sampler_canonical sampler k budget hK hBudget
      subst sampler
      exact (GeneralPaperEqualFullBitOutput.native_written_output true model W k values v hv small budget hB hHeight
        (trace.1 + 1) (GeneralPaperEqualBooleanTraceCost.tapeFor _ _ trace)
        (GeneralPaperEqualRejectionTraceMeasure.scalar _ _ trace.1 trace.2) row h).2

end Blotto.GeneralPaperEqualSelectedDraw
