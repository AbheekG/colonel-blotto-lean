import Blotto.RationalRejectionSchedule

/-! The constructed dyadic schedule realizes the final finite draw contract.
Accuracy 2^-E is achieved from computed trial count and coin precision, with
no caller-supplied schedule inequality. Representation/cost bounds stay separate. -/

namespace Blotto
open scoped Classical
namespace RationalWeightedGuideTree

def scheduledAttempts (tree : RationalWeightedGuideTree) (E : ℕ) : ℕ := rejectionScheduleAttempts tree.factor E

def scheduledPrecision (tree : RationalWeightedGuideTree) (E : ℕ) : ℕ :=
  rejectionSchedulePrecision tree.nodes (tree.scheduledAttempts E) E

def scheduledBitBudget (tree : RationalWeightedGuideTree) (E : ℕ) : ℕ :=
  tree.scheduledAttempts E * tree.attemptBitBudget (tree.scheduledPrecision E)

def scheduledOutput (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (E : ℕ)
    (fallback : Fin tree.trueSize) (bits : Fin (tree.scheduledBitBudget E) → Bool) : Fin tree.trueSize :=
  tree.rejectionNativeOutput hc B hm (tree.scheduledPrecision E) (tree.scheduledAttempts E) fallback bits

theorem scheduledOutput_event_error (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (E : ℕ)
    (fallback : Fin tree.trueSize) (event : Set (Fin tree.real.trueSize)) :
    |(fairBitKernel (tree.scheduledBitBudget E)).mean
      (fun bits => if (tree.scheduledOutput hc B hm E fallback bits).cast tree.real_trueSize.symm ∈ event then 1 else 0) -
      (tree.targetKernel B hm).mean (fun x => if x ∈ event then 1 else 0)| ≤ 1 / (2 : ℝ) ^ E := by
  have hf : (1 : ℚ) ≤ tree.factor := by
    have he := tree.real.factor_ge_one hc
    rw [← tree.factor_real] at he
    exact_mod_cast he
  exact (tree.rejectionNativeOutput_event_error hc B hm _ _ fallback event).trans
    (rejectionSchedule_total_error tree.factor hf tree.nodes E)

theorem scheduledOutput_feasible (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (E : ℕ)
    (fallback : Fin tree.trueSize)
    (hf : tree.real.trueFamily.resource (fallback.cast tree.real_trueSize.symm) ≤ (B : ℝ))
    (bits : Fin (tree.scheduledBitBudget E) → Bool) :
    tree.real.trueFamily.resource ((tree.scheduledOutput hc B hm E fallback bits).cast tree.real_trueSize.symm) ≤ (B : ℝ) :=
  tree.rejectionNativeOutput_feasible hc B hm _ _ fallback hf bits

end RationalWeightedGuideTree
end Blotto
