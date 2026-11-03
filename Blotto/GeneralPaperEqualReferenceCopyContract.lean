import Blotto.GeneralPaperEqualSelectedCopy

/-! Append the executed retained-data copy to an already prepared return.
The source width comes from its preparation controller. Exact total work
includes the new copy. Native sharp rates/lifetimes and complete measured
field-to-layout/draw-access joins remain subsequent obligations. -/
namespace Blotto.GeneralPaperEqualReferenceCopyContract
open MeasureTheory
open GeneralPaperEqualInputDomain GeneralPaperEqualInputHeadline
open GeneralPaperEqualSelectedSampler (Sampler traceLaw observed outputLaw realDecode)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def finish {n : ℕ} (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (original : Sampler v k budget × ℕ) :=
  let copied := GeneralPaperEqualSelectedCopy.run S original.1
  (copied.1,original.2 + copied.2)

theorem data {n : ℕ} (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (original : Sampler v k budget × ℕ) :
    (finish S original).1 = original.1 := GeneralPaperEqualSelectedCopy.data S original.1

theorem work {n : ℕ} (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (original : Sampler v k budget × ℕ) :
    (finish S original).2 = original.2 + (GeneralPaperEqualSelectedCopy.run S original.1).2 := rfl

theorem retained_copy_charged {n : ℕ} (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (original : Sampler v k budget × ℕ) :
    GeneralPaperEqualSelectedDescription.footprint (finish S original).1 ≤
      128 * (GeneralPaperEqualSelectedCopy.run S original.1).2 := GeneralPaperEqualSelectedCopy.charged S original.1

theorem actual_return_contract (model : RationalCostModel) (S A K : ℕ) (p : Input model) :
    let original := GeneralPaperEqualSelectedPipeline.run model A K p
    let result := finish S original
    let a := result.1
    result.2 = original.2 + (GeneralPaperEqualSelectedCopy.run S original.1).2 ∧
    a = original.1 ∧
    GeneralPaperEqualSelectedDescription.footprint a ≤
      2 * GeneralPaperEqualDescriptionRates.paperBound p.n p.k (rationalWordWidth p.budget) ∧
    GeneralPaperEqualSelectedDescription.footprint a < 2 ^ a.address ∧
    (traceLaw a).map (realDecode model a) = outputLaw model a ∧
    (∀ᵐ trace ∂(traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch)),
      ∃ row, (observed model a trace).output = some row) ∧
    (0 ≤ p.budget → ∀ trace row, (observed model a trace).output = some row →
      FullBudget (p.budget : ℝ) row.realAllocation ∧
        ∀ j,RationalHeight (row.allocation j)
          (33554432 * (rationalWordWidth p.budget + binaryWordWidth p.n + p.k + 10))) ∧
    (epsilon p < 1 → 0 < p.budget →
      Supported (p.budget : ℝ) (outputLaw model a) ∧
      regret p.selector.values (p.budget : ℝ) (outputLaw model a) (outputLaw model a) ≤ (epsilon p : ℝ)) := by
  dsimp only
  refine ⟨work S _,data S _,
    GeneralPaperEqualSelectedDescription.paper_bound model _ p.k p.values p.selector p.correct p.budget _,
    GeneralPaperEqualSelectedDescription.capacity model _ p.k p.values p.selector p.correct p.budget _,
    GeneralPaperEqualSelectedSampler.law model _,GeneralPaperEqualSelectedSampler.completed_ae model _,
    fun hB trace row h => GeneralPaperEqualSelectedDraw.written_output model _ p.k p.values p.selector p.correct p.budget
      hB (rationalHeight_of_wordWidth p.budget) _ trace row h,?_⟩
  rw [data]
  exact fun hOne hB => GeneralPaperEqualSelectedPipeline.epsilon model A K p hOne hB

end Blotto.GeneralPaperEqualReferenceCopyContract
