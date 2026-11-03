import Blotto.RationalRejectionFeasibility

/-! The executable native label output carries the same all-event accuracy
and every-path hard resource guarantee as the proved semantic output. Both
block precision and attempt cap are visible parameters; cost bounds remain open. -/

namespace Blotto
open scoped Classical
namespace RationalWeightedGuideTree

theorem rejectionNativeOutput_event_error (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K attempts : ℕ)
    (fallback : Fin tree.trueSize) (event : Set (Fin tree.real.trueSize)) :
    |(fairBitKernel (attempts * tree.attemptBitBudget K)).mean
      (fun bits => if (tree.rejectionNativeOutput hc B hm K attempts fallback bits).cast tree.real_trueSize.symm ∈ event then 1 else 0) -
      (tree.targetKernel B hm).mean (fun x => if x ∈ event then 1 else 0)| ≤
        (attempts : ℝ) * (((tree.nodes : ℝ) + 1) * (1 / (2 : ℝ) ^ K)) +
          (1 - 1 / (tree.factor : ℝ)) ^ attempts := by
  simp_rw [tree.rejectionNativeOutput_eq]
  exact tree.rejectionOutput_event_error hc B hm K attempts _ event

theorem rejectionNativeOutput_contract (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K attempts : ℕ)
    (fallback : Fin tree.trueSize)
    (hf : tree.real.trueFamily.resource (fallback.cast tree.real_trueSize.symm) ≤ (B : ℝ)) :
    (∀ bits : Fin (attempts * tree.attemptBitBudget K) → Bool,
      tree.real.trueFamily.resource ((tree.rejectionNativeOutput hc B hm K attempts fallback bits).cast tree.real_trueSize.symm) ≤ (B : ℝ)) ∧
    (∀ event : Set (Fin tree.real.trueSize),
      |(fairBitKernel (attempts * tree.attemptBitBudget K)).mean
        (fun bits => if (tree.rejectionNativeOutput hc B hm K attempts fallback bits).cast tree.real_trueSize.symm ∈ event then 1 else 0) -
        (tree.targetKernel B hm).mean (fun x => if x ∈ event then 1 else 0)| ≤
          (attempts : ℝ) * (((tree.nodes : ℝ) + 1) * (1 / (2 : ℝ) ^ K)) +
            (1 - 1 / (tree.factor : ℝ)) ^ attempts) :=
  ⟨tree.rejectionNativeOutput_feasible hc B hm K attempts fallback hf,
    tree.rejectionNativeOutput_event_error hc B hm K attempts fallback⟩

end RationalWeightedGuideTree
end Blotto
