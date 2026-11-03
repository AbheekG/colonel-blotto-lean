import Blotto.GeneralPaperMeasuredTwoPoolLayout

/-! Actual complete selected field plans instantiate the two-pool layout.
The inner boundary is computed by the first layout, and both capacities are
derived from the actual native selected return. No supplied size/capacity
certificate is an execution input. Field-pointer installation/draw access and
the new passes' full resource/pipeline joins remain separate obligations. -/
namespace Blotto.GeneralPaperEqualMeasuredLayout
open GeneralPaperMeasuredBlockPlan GeneralPaperSequentialLayout
open GeneralPaperEqualSelectedSampler (Sampler)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def innerWidth {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (a : Sampler v k budget) : ℕ :=
  match a.branch with
  | .dominant _ _ _ _ => a.address
  | .grouped _ source _ _ => source.address

theorem widths_positive {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (a : Sampler v k budget) :
    1 ≤ innerWidth a ∧ 1 ≤ a.address := by
  have hOuter : 1 ≤ a.address := by rw [a.address_correct]; omega
  refine ⟨?_,hOuter⟩
  cases a with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy source correct => exact hOuter
    | grouped small source hK hB =>
      change 1 ≤ source.address
      rw [source.address_correct]
      exact binaryWordWidth_pos _

def inner {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) : Plan := GeneralPaperEqualMeasuredSelectedPlan.branch model S a.address a.branch
def outer {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) : Plan := GeneralPaperEqualMeasuredSelectedPlan.header model S a.address

def run {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) : GeneralPaperMeasuredTwoPoolLayout.Result (innerWidth a) a.address :=
  GeneralPaperMeasuredTwoPoolLayout.run model S (innerWidth a) a.address (inner model S a) (outer model S a)

theorem boundary {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) :
    (run model S a).boundary = GeneralPaperEqualSelectedDescription.branchFootprint a.address a.branch := by
  rw [run,GeneralPaperMeasuredTwoPoolLayout.boundary]
  exact GeneralPaperEqualMeasuredSelectedPlan.branch_sum model S a.address a.branch

theorem finish {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) : (run model S a).finish = GeneralPaperEqualSelectedDescription.footprint a := by
  rw [run,GeneralPaperMeasuredTwoPoolLayout.finish]
  dsimp only [inner,outer]
  rw [GeneralPaperEqualMeasuredSelectedPlan.branch_sum,GeneralPaperEqualMeasuredSelectedPlan.header_sum]
  rfl

theorem inner_capacity {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    (inner model S a).sizes.sum < 2 ^ innerWidth a := by
  have hTotal := GeneralPaperEqualSelectedDescription.capacity model W k values v hv budget a
  dsimp only [inner]
  rw [GeneralPaperEqualMeasuredSelectedPlan.branch_sum]
  cases a with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy source correct =>
      dsimp only [innerWidth,GeneralPaperEqualSelectedDescription.footprint] at hTotal ⊢
      omega
    | grouped small source hK hB =>
      dsimp only [innerWidth,GeneralPaperEqualSelectedDescription.branchFootprint]
      have hs := GeneralPaperEqualBitCanonical.sampler_canonical source k budget hK hB
      subst source
      have h := GeneralPaperEqualNativeDrawRepresentation.native_capacity true model W k values v hv small budget
      dsimp only [GeneralPaperEqualStoredBitSampler.native,GeneralPaperEqualNativeCache.prepare] at h
      exact h

theorem total_capacity {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    (inner model S a).sizes.sum + (outer model S a).sizes.sum < 2 ^ a.address := by
  dsimp only [inner,outer]
  rw [GeneralPaperEqualMeasuredSelectedPlan.branch_sum,GeneralPaperEqualMeasuredSelectedPlan.header_sum]
  exact GeneralPaperEqualSelectedDescription.capacity model W k values v hv budget a

theorem references {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    (∀ r ∈ (run model S a).inner,r.reference.value = r.start) ∧
      (∀ r ∈ (run model S a).outer,r.reference.value = r.start) :=
  ⟨GeneralPaperMeasuredTwoPoolLayout.inner_references model S _ _ _ _ (inner_capacity model W S k values v hv budget a),
    GeneralPaperMeasuredTwoPoolLayout.outer_references model S _ _ _ _ (total_capacity model W S k values v hv budget a)⟩

theorem disjoint_pools {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) : ∀ r ∈ (run model S a).inner,∀ s ∈ (run model S a).outer,
      Disjoint (Set.Ico r.start r.stop) (Set.Ico s.start s.stop) :=
  GeneralPaperMeasuredTwoPoolLayout.disjoint_pools model S _ _ _ _

theorem work {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    (run model S a).work ≤ (inner model S a).work + (outer model S a).work +
      ((inner model S a).sizes.length + 1) * stepPrice model S (innerWidth a) +
      ((outer model S a).sizes.length + 1) * stepPrice model S a.address + 192 * (S + innerWidth a + a.address + 1) :=
  GeneralPaperMeasuredTwoPoolLayout.work model S _ _ _ _ (widths_positive a).1 (widths_positive a).2
    (inner_capacity model W S k values v hv budget a) (total_capacity model W S k values v hv budget a)

theorem actual_source_and_copied_plan (model : RationalCostModel) (A K : ℕ) (p : GeneralPaperEqualInputDomain.Input model) :
    (GeneralPaperEqualMeasuredSelectedPlan.run model (GeneralPaperEqualInputDomain.word K p)
      (GeneralPaperEqualCopiedPipeline.run model A K p).1).sizes =
    (GeneralPaperEqualMeasuredSelectedPlan.run model (GeneralPaperEqualInputDomain.word K p)
      (GeneralPaperEqualSelectedPipeline.run model A K p).1).sizes := by
  rw [GeneralPaperEqualCopiedPipeline.selected_data]

theorem actual_source_layout (model : RationalCostModel) (A K : ℕ) (p : GeneralPaperEqualInputDomain.Input model) :
    let W := GeneralPaperEqualInputDomain.word K p
    let a := (GeneralPaperEqualSelectedPipeline.run model A K p).1
    (run model W a).finish = GeneralPaperEqualSelectedDescription.footprint (GeneralPaperEqualCopiedPipeline.run model A K p).1 ∧
      (∀ r ∈ (run model W a).inner,r.reference.value = r.start) ∧
      (∀ r ∈ (run model W a).outer,r.reference.value = r.start) := by
  dsimp only
  refine ⟨?_,references model _ _ p.k p.values p.selector p.correct p.budget _⟩
  rw [finish,GeneralPaperEqualCopiedPipeline.selected_data]

theorem actual_source_layout_size (model : RationalCostModel) (A K : ℕ) (p : GeneralPaperEqualInputDomain.Input model) :
    let W := GeneralPaperEqualInputDomain.word K p
    let a := (GeneralPaperEqualSelectedPipeline.run model A K p).1
    (run model W a).finish ≤ 2 * GeneralPaperEqualDescriptionRates.paperBound p.n p.k (rationalWordWidth p.budget) ∧
      (run model W a).finish < 2 ^ a.address := by
  dsimp only
  rw [finish]
  exact ⟨GeneralPaperEqualSelectedDescription.paper_bound model _ p.k p.values p.selector p.correct p.budget _,
    GeneralPaperEqualSelectedDescription.capacity model _ p.k p.values p.selector p.correct p.budget _⟩

end Blotto.GeneralPaperEqualMeasuredLayout
