import Blotto.RationalScheduledRejection

/-! Positive rational accuracy selects the dyadic output schedule using the
maintained bit-width precision algorithm. No search over geometric tails or
numerical inverse-accuracy trial loop is hidden in this wrapper. -/

namespace Blotto
open scoped Classical
namespace RationalWeightedGuideTree

def epsilonPrecision (epsilon : ℚ) : ℕ := rationalAccuracyPrecision (32 * epsilon)

theorem epsilonPrecision_guard (epsilon : ℚ) (he : 0 < epsilon) :
    1 / (2 : ℝ) ^ epsilonPrecision epsilon ≤ (epsilon : ℝ) := by
  have hp : 0 < 32 * epsilon := by positivity
  have hg := rationalAccuracyPrecision_real_guard (32 * epsilon) hp
  have heq : (((32 * epsilon : ℚ) : ℝ)) = 32 * (epsilon : ℝ) := by norm_cast
  rw [heq] at hg
  have hPower : 0 < (2 : ℝ) ^ epsilonPrecision epsilon := by positivity
  apply (div_le_iff₀ hPower).mpr
  unfold epsilonPrecision at hPower ⊢
  nlinarith

def epsilonBitBudget (tree : RationalWeightedGuideTree) (epsilon : ℚ) : ℕ :=
  tree.scheduledBitBudget (epsilonPrecision epsilon)

def epsilonOutput (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (epsilon : ℚ)
    (fallback : Fin tree.trueSize) (bits : Fin (tree.epsilonBitBudget epsilon) → Bool) : Fin tree.trueSize :=
  tree.scheduledOutput hc B hm (epsilonPrecision epsilon) fallback bits

theorem epsilonOutput_event_error (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (epsilon : ℚ) (he : 0 < epsilon)
    (fallback : Fin tree.trueSize) (event : Set (Fin tree.real.trueSize)) :
    |(fairBitKernel (tree.epsilonBitBudget epsilon)).mean
      (fun bits => if (tree.epsilonOutput hc B hm epsilon fallback bits).cast tree.real_trueSize.symm ∈ event then 1 else 0) -
      (tree.targetKernel B hm).mean (fun x => if x ∈ event then 1 else 0)| ≤ (epsilon : ℝ) :=
  (tree.scheduledOutput_event_error hc B hm _ fallback event).trans (epsilonPrecision_guard epsilon he)

end RationalWeightedGuideTree
end Blotto
