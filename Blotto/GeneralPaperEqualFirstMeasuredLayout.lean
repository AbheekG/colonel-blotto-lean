import Blotto.GeneralPaperEqualFirstInputContract

/-! The actual measured two-pool layout is valid for the corrected source.
All roots, disjointness, capacities and layout work follow from actual fields;
midpoint precision and local reference formulas remain unchanged. -/
namespace Blotto.GeneralPaperEqualFirstMeasuredLayout
open GeneralPaperEqualMeasuredLayout (innerWidth inner outer run widths_positive)
open GeneralPaperMeasuredBlockPlan GeneralPaperSequentialLayout
open GeneralPaperEqualSelectedSampler (Sampler)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem inner_capacity {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    (inner model S a).sizes.sum < 2 ^ innerWidth a := by
  have hTotal := GeneralPaperEqualFirstSelectedDescription.capacity model W k values v hv budget a
  dsimp only [GeneralPaperEqualMeasuredLayout.inner]
  rw [GeneralPaperEqualMeasuredSelectedPlan.branch_sum]
  cases a with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy source correct =>
      dsimp only [innerWidth,GeneralPaperEqualSelectedDescription.footprint] at hTotal ⊢
      omega
    | grouped small source hK hB =>
      dsimp only [innerWidth,GeneralPaperEqualSelectedDescription.branchFootprint]
      exact GeneralPaperEqualFirstDrawRepresentation.capacity model W k values v hv small budget source hK hB

theorem total_capacity {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    (inner model S a).sizes.sum + (outer model S a).sizes.sum < 2 ^ a.address := by
  dsimp only [GeneralPaperEqualMeasuredLayout.inner,GeneralPaperEqualMeasuredLayout.outer]
  rw [GeneralPaperEqualMeasuredSelectedPlan.branch_sum,GeneralPaperEqualMeasuredSelectedPlan.header_sum]
  exact GeneralPaperEqualFirstSelectedDescription.capacity model W k values v hv budget a

theorem references {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
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
    (budget : ℚ) (a : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    (run model S a).work ≤ (inner model S a).work + (outer model S a).work +
      ((inner model S a).sizes.length + 1) * stepPrice model S (innerWidth a) +
      ((outer model S a).sizes.length + 1) * stepPrice model S a.address + 192 * (S + innerWidth a + a.address + 1) :=
  GeneralPaperMeasuredTwoPoolLayout.work model S _ _ _ _ (widths_positive a).1 (widths_positive a).2
    (inner_capacity model W S k values v hv budget a) (total_capacity model W S k values v hv budget a)


end Blotto.GeneralPaperEqualFirstMeasuredLayout
