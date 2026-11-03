import Blotto.RationalRejectionPrecision

/-! Every final output of the capped native rejection sampler is feasible
when its supplied fallback label is feasible, including exhaustion and every
zero-probability seed. The true label carries the complete product allocation. -/

namespace Blotto
namespace RationalWeightedGuideTree

theorem rejectionOutput_feasible (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K attempts : ℕ)
    (fallback : Fin tree.real.trueSize) (hf : tree.real.trueFamily.resource fallback ≤ (B : ℝ))
    (bits : Fin (attempts * tree.attemptBitBudget K) → Bool) :
    tree.real.trueFamily.resource (tree.rejectionOutput hc B hm K attempts fallback bits) ≤ (B : ℝ) := by
  unfold rejectionOutput
  cases he : tree.rejectionFinite hc B hm K attempts bits with
  | none => exact hf
  | some record =>
    have hq := tree.rejectionFinite_feasible hc B hm K attempts bits record he
    have hr : (tree.resource record : ℝ) ≤ (B : ℝ) := by exact_mod_cast hq
    rw [tree.resource_real] at hr
    exact hr

theorem rejectionNativeOutput_feasible (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K attempts : ℕ)
    (fallback : Fin tree.trueSize)
    (hf : tree.real.trueFamily.resource (fallback.cast tree.real_trueSize.symm) ≤ (B : ℝ))
    (bits : Fin (attempts * tree.attemptBitBudget K) → Bool) :
    tree.real.trueFamily.resource ((tree.rejectionNativeOutput hc B hm K attempts fallback bits).cast tree.real_trueSize.symm) ≤ (B : ℝ) := by
  rw [tree.rejectionNativeOutput_eq]
  exact tree.rejectionOutput_feasible hc B hm K attempts _ hf bits

end RationalWeightedGuideTree
end Blotto
