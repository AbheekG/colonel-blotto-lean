import Blotto.ImplicitProposalRejectionLaw
import Blotto.ImplicitRejectionSchedule

/-! Bounded native implicit-leaf rejection draws the exact feasible product
target to requested dyadic/rational accuracy, with a complete fixed seed budget.
The original guide certificate and feasible fallback are explicit. Actual source
guide construction, original-budget compiler and binary prices remain separate. -/

namespace Blotto.ImplicitLeafCounts.ProposalTree
open scoped Classical

def scheduledOutput (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (E : ℕ)
    (fallback : Fin tree.projected.trueSize) (bits : Fin (tree.rejectionSeedBudget E) → Bool) : Fin tree.projected.trueSize :=
  tree.nativeOutput hc budget hm (tree.rejectionPrecision E) (tree.rejectionPrecision E)
    (tree.rejectionAttempts E) fallback bits

theorem scheduledOutput_mean_error (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (E : ℕ)
    (fallback : Fin tree.projected.trueSize) (test : Fin tree.projected.real.trueSize → ℝ)
    (hTest : ∀ label, 0 ≤ test label ∧ test label ≤ 1) :
    |(fairBitKernel (tree.rejectionSeedBudget E)).mean
      (fun bits => test ((tree.scheduledOutput hc budget hm E fallback bits).cast tree.projected.real_trueSize.symm)) -
        (tree.projected.targetKernel budget hm).mean test| ≤ 1 / (2 : ℝ) ^ E :=
  (tree.nativeOutput_mean_error hc budget hm _ _ _ fallback test hTest).trans (tree.rejection_schedule_error hc E)

theorem scheduledOutput_feasible (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (E : ℕ)
    (fallback : Fin tree.projected.trueSize)
    (hFallback : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ))
    (bits : Fin (tree.rejectionSeedBudget E) → Bool) :
    tree.projected.real.trueFamily.resource
      ((tree.scheduledOutput hc budget hm E fallback bits).cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ) :=
  tree.nativeOutput_feasible hc budget hm _ _ _ fallback hFallback bits

def epsilonSeedBudget (tree : ProposalTree) (epsilon : ℚ) : ℕ :=
  tree.rejectionSeedBudget (RationalWeightedGuideTree.epsilonPrecision epsilon)

def epsilonOutput (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ)
    (fallback : Fin tree.projected.trueSize) (bits : Fin (tree.epsilonSeedBudget epsilon) → Bool) : Fin tree.projected.trueSize :=
  tree.scheduledOutput hc budget hm (RationalWeightedGuideTree.epsilonPrecision epsilon) fallback bits

theorem epsilonOutput_contract (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ) (he : 0 < epsilon)
    (fallback : Fin tree.projected.trueSize)
    (hFallback : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ)) :
    (∀ bits : Fin (tree.epsilonSeedBudget epsilon) → Bool, tree.projected.real.trueFamily.resource
      ((tree.epsilonOutput hc budget hm epsilon fallback bits).cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ)) ∧
    (∀ test : Fin tree.projected.real.trueSize → ℝ, (∀ label, 0 ≤ test label ∧ test label ≤ 1) →
      |(fairBitKernel (tree.epsilonSeedBudget epsilon)).mean
        (fun bits => test ((tree.epsilonOutput hc budget hm epsilon fallback bits).cast tree.projected.real_trueSize.symm)) -
          (tree.projected.targetKernel budget hm).mean test| ≤ (epsilon : ℝ)) := by
  refine ⟨fun bits => tree.scheduledOutput_feasible hc budget hm _ fallback hFallback bits, ?_⟩
  intro test hTest
  exact (tree.scheduledOutput_mean_error hc budget hm _ fallback test hTest).trans
    (RationalWeightedGuideTree.epsilonPrecision_guard epsilon he)

end Blotto.ImplicitLeafCounts.ProposalTree
