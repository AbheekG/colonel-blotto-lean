import Blotto.RationalProposalNativeOutput

/-! The bounded native draw has explicit whole-label event accuracy: finite-bit
attempt error plus a geometric ideal rejection tail. Feasible fallback remains
pointwise; no success conditioning enters the precision contract. -/

namespace Blotto
open scoped BigOperators Classical
namespace RationalWeightedGuideTree

theorem idealFailure_factor_bound (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (attempts : ℕ) :
    rejectionFailure (tree.idealAcceptance B) attempts ≤ (1 - 1 / (tree.factor : ℝ)) ^ attempts := by
  have hb := tree.idealAcceptance_bounds hc B hm
  have hf : 0 < (tree.factor : ℝ) := by rw [tree.factor_real]; linarith [tree.real.factor_ge_one hc]
  exact rejectionFailure_mono_probability (by positivity) hb.2.2 hb.2.1 attempts

theorem rejectionOutput_event_error (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K attempts : ℕ)
    (fallback : Fin tree.real.trueSize) (event : Set (Fin tree.real.trueSize)) :
    |(fairBitKernel (attempts * tree.attemptBitBudget K)).mean
      (fun bits => if tree.rejectionOutput hc B hm K attempts fallback bits ∈ event then 1 else 0) -
      (tree.targetKernel B hm).mean (fun x => if x ∈ event then 1 else 0)| ≤
        (attempts : ℝ) * (((tree.nodes : ℝ) + 1) * (1 / (2 : ℝ) ^ K)) +
          (1 - 1 / (tree.factor : ℝ)) ^ attempts := by
  have he := tree.rejectionOutput_mean_error hc B hm K attempts fallback
    (fun x => if x ∈ event then 1 else 0) (by intro x; split_ifs <;> norm_num)
  exact he.trans (add_le_add (le_refl _) (tree.idealFailure_factor_bound hc B hm attempts))

theorem rejectionOutput_precision (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K attempts : ℕ)
    (fallback : Fin tree.real.trueSize) (event : Set (Fin tree.real.trueSize)) (epsilon : ℝ)
    (hPrecision : (attempts : ℝ) * (((tree.nodes : ℝ) + 1) * (1 / (2 : ℝ) ^ K)) +
      (1 - 1 / (tree.factor : ℝ)) ^ attempts ≤ epsilon) :
    |(fairBitKernel (attempts * tree.attemptBitBudget K)).mean
      (fun bits => if tree.rejectionOutput hc B hm K attempts fallback bits ∈ event then 1 else 0) -
      (tree.targetKernel B hm).mean (fun x => if x ∈ event then 1 else 0)| ≤ epsilon :=
  (tree.rejectionOutput_event_error hc B hm K attempts fallback event).trans hPrecision

end RationalWeightedGuideTree
end Blotto
