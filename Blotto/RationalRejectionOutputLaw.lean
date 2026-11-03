import Blotto.RationalRejectionIdealTarget
import Blotto.RationalBoundedRejection
import Blotto.RejectionKernelMapping

/-! The actual bounded native rejection/fallback draw approximates the original
feasible product target. Error includes both bounded-bit attempt error and the
ideal geometric exhaustion tail; success is never used as an uncharged condition. -/

namespace Blotto
open scoped BigOperators Classical
namespace RationalWeightedGuideTree

noncomputable def rejectionOutput (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K attempts : ℕ)
    (fallback : Fin tree.real.trueSize) (bits : Fin (attempts * tree.attemptBitBudget K) → Bool) : Fin tree.real.trueSize :=
  ((tree.rejectionFinite hc B hm K attempts bits).map tree.trueOutput).getD fallback

theorem rejectionOutput_mean_error (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K attempts : ℕ)
    (fallback : Fin tree.real.trueSize) (f : Fin tree.real.trueSize → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |(fairBitKernel (attempts * tree.attemptBitBudget K)).mean
      (fun bits => f (tree.rejectionOutput hc B hm K attempts fallback bits)) - (tree.targetKernel B hm).mean f| ≤
        (attempts : ℝ) * (((tree.nodes : ℝ) + 1) * (1 / (2 : ℝ) ^ K)) +
          rejectionFailure (tree.idealAcceptance B) attempts := by
  let test : Option tree.Record → ℝ := fun result => f ((result.map tree.trueOutput).getD fallback)
  have hn := tree.rejectionFinite_mean_error hc B hm K attempts test (fun result => hf _)
  let mapped := (tree.attemptKernel false hc B hm K).map (fun result => result.map tree.trueOutput)
  have hAttempt : ∀ g, mapped.mean g = tree.idealAcceptance B *
      (tree.targetKernel B hm).mean (fun x => g (some x)) + (1 - tree.idealAcceptance B) * g none :=
    tree.attemptKernel_ideal_target_mean hc B hm K
  have hp := tree.idealAcceptance_bounds hc B hm
  have ht := BoundedExpectationKernel.firstSuccess_fallback_error mapped (tree.targetKernel B hm)
    (tree.idealAcceptance B) hp.1.le hp.2.1 hAttempt attempts fallback f hf
  have hMap := BoundedExpectationKernel.firstSuccess_map_mean (tree.attemptKernel false hc B hm K)
    tree.trueOutput attempts (fun result => f (result.getD fallback))
  change ((tree.attemptKernel false hc B hm K).firstSuccess attempts).mean test =
    (mapped.firstSuccess attempts).mean (fun result => f (result.getD fallback)) at hMap
  change |(mapped.firstSuccess attempts).mean (fun result => f (result.getD fallback)) -
    (tree.targetKernel B hm).mean f| ≤ _ at ht
  rw [← hMap] at ht
  have hTri := abs_sub_le
    ((fairBitKernel (attempts * tree.attemptBitBudget K)).mean (fun bits => test (tree.rejectionFinite hc B hm K attempts bits)))
    (((tree.attemptKernel false hc B hm K).firstSuccess attempts).mean test)
    ((tree.targetKernel B hm).mean f)
  exact hTri.trans (add_le_add hn ht)

end RationalWeightedGuideTree
end Blotto
