import Blotto.GeneralPaperEqualMeasuredRetainedPlan

/-! Complete selected-closure measured plan. Grouped internals retain their
stored inner reference width; only the outer record uses the selected width.
The pure row and chosen label use the stored outer reference throughout. -/
namespace Blotto.GeneralPaperEqualMeasuredSelectedPlan
open GeneralPaperMeasuredBlockPlan GeneralPaperEqualMeasuredLeafPlans
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def branch {n : ℕ} (model : RationalCostModel) (S A : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} :
    GeneralPaperEqualBitBranch.Prepared v k budget → Plan
  | .dominant chosen _ source _ =>
    sequence S [GeneralPaperMeasuredArrayBlockPlan.array model S A (rational model S)
      (⟨source.data,source.size⟩ : FixedArrayTable n ℚ),natural model S chosen.val,reserve model S A 32]
  | .grouped _ source _ _ => GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source

theorem branch_sum {n : ℕ} (model : RationalCostModel) (S A : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (p : GeneralPaperEqualBitBranch.Prepared v k budget) :
    (branch model S A p).sizes.sum = GeneralPaperEqualSelectedDescription.branchFootprint A p := by
  cases p with
  | dominant chosen heavy source correct =>
    have hr := GeneralPaperMeasuredArrayBlockPlan.array_sum model S A (rational model S) rationalWordWidth
      (⟨source.data,source.size⟩ : FixedArrayTable n ℚ)
      (by intro i; rw [rational_data]; simp only [List.sum_cons,List.sum_nil,Nat.add_zero])
    simp only [branch,sequence_sum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hr,natural_data,reserve_sum,
      Nat.add_zero,GeneralPaperEqualSelectedDescription.branchFootprint]
    omega
  | grouped small source hK hB => exact GeneralPaperEqualMeasuredRetainedPlan.sampler_sum model S source.address source

def header (model : RationalCostModel) (S A : ℕ) : Plan :=
  join S (GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (natural model S) [A]) (reserve model S A 64)

theorem header_sum (model : RationalCostModel) (S A : ℕ) :
    (header model S A).sizes.sum = GeneralPaperEqualSelectedDescription.header A := by
  dsimp only [header]
  rw [join_sum,GeneralPaperMeasuredListBlockPlan.fields_sum,reserve_sum]
  rfl

def run {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) : Plan :=
  join S (branch model S a.address a.branch) (header model S a.address)

theorem sum {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) : (run model S a).sizes.sum = GeneralPaperEqualSelectedDescription.footprint a := by
  dsimp only [run]
  rw [join_sum,branch_sum,header_sum]
  rfl

end Blotto.GeneralPaperEqualMeasuredSelectedPlan
