import Blotto.ImplicitProposalRejection

/-! The implicit native root-rejection draw approximates the original feasible
product target for all bounded tests. Precision errors and the ideal geometric
exhaustion tail are explicit; every output, including fallback, is feasible. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts
namespace ProposalTree

theorem ideal_attempt_projected (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts : ℕ)
    (test : Option tree.projected.Record → ℝ) :
    (tree.attemptKernel false hc budget hm K leafAttempts).mean (fun result => test (result.map tree.toProjected)) =
      (tree.projected.attemptKernel false hc budget hm K).mean test := by
  let next := acceptanceKernel (fun record => (tree.projected.acceptanceProbability budget record : ℝ))
    (fun record => by exact_mod_cast tree.projected.acceptanceProbability_unit hc budget hm record)
  have hAcceptance : ∀ result : Option tree.Record,
      (acceptanceKernel (fun record => (tree.acceptProbability budget record : ℝ))
        (fun record => by exact_mod_cast tree.acceptProbability_unit hc budget hm record) result).mean
          (fun output => test (output.map tree.toProjected)) = (next (result.map tree.toProjected)).mean test := by
    intro result
    cases result <;> rfl
  change (tree.kernel false budget K leafAttempts).mean (fun result =>
    (acceptanceKernel (fun record => (tree.acceptProbability budget record : ℝ))
      (fun record => by exact_mod_cast tree.acceptProbability_unit hc budget hm record) result).mean
        (fun output => test (output.map tree.toProjected))) = _
  simp_rw [hAcceptance]
  exact tree.ideal_kernel_projected budget K leafAttempts (fun result => (next result).mean test)

noncomputable def outputLabel (tree : ProposalTree) (record : tree.Record) : Fin tree.projected.real.trueSize :=
  tree.projected.trueOutput (tree.toProjected record)

noncomputable def output (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts attempts : ℕ)
    (fallback : Fin tree.projected.real.trueSize)
    (bits : Fin (attempts * tree.attemptBitBudget K leafAttempts) → Bool) : Fin tree.projected.real.trueSize :=
  ((tree.rejection hc budget hm K leafAttempts attempts bits).map tree.outputLabel).getD fallback

theorem ideal_attempt_target (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts : ℕ)
    (test : Option (Fin tree.projected.real.trueSize) → ℝ) :
    ((tree.attemptKernel false hc budget hm K leafAttempts).map (fun result => result.map tree.outputLabel)).mean test =
      tree.projected.idealAcceptance budget * (tree.projected.targetKernel budget hm).mean (fun label => test (some label)) +
        (1 - tree.projected.idealAcceptance budget) * test none := by
  have he := tree.ideal_attempt_projected hc budget hm K leafAttempts
    (fun result => test (result.map tree.projected.trueOutput))
  have hCompose : (fun result : Option tree.Record => test ((result.map tree.toProjected).map tree.projected.trueOutput)) =
      fun result => test (result.map tree.outputLabel) := by
    funext result
    cases result <;> rfl
  rw [hCompose] at he
  exact he.trans (tree.projected.attemptKernel_ideal_target_mean hc budget hm K test)

theorem output_mean_error (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts attempts : ℕ)
    (fallback : Fin tree.projected.real.trueSize) (test : Fin tree.projected.real.trueSize → ℝ)
    (hTest : ∀ label, 0 ≤ test label ∧ test label ≤ 1) :
    |(fairBitKernel (attempts * tree.attemptBitBudget K leafAttempts)).mean
      (fun bits => test (tree.output hc budget hm K leafAttempts attempts fallback bits)) -
        (tree.projected.targetKernel budget hm).mean test| ≤
          (attempts : ℝ) * (tree.error K leafAttempts + 1 / (2 : ℝ) ^ K) +
            rejectionFailure (tree.projected.idealAcceptance budget) attempts := by
  let lifted : Option tree.Record → ℝ := fun result => test ((result.map tree.outputLabel).getD fallback)
  have hNative := tree.rejection_mean_error hc budget hm K leafAttempts attempts lifted (fun result => hTest _)
  let mapped := (tree.attemptKernel false hc budget hm K leafAttempts).map (fun result => result.map tree.outputLabel)
  have hAttempt : ∀ f, mapped.mean f = tree.projected.idealAcceptance budget *
      (tree.projected.targetKernel budget hm).mean (fun label => f (some label)) +
        (1 - tree.projected.idealAcceptance budget) * f none := tree.ideal_attempt_target hc budget hm K leafAttempts
  have ha := tree.projected.idealAcceptance_bounds hc budget hm
  have hIdeal := BoundedExpectationKernel.firstSuccess_fallback_error mapped (tree.projected.targetKernel budget hm)
    (tree.projected.idealAcceptance budget) ha.1.le ha.2.1 hAttempt attempts fallback test hTest
  have hMap := BoundedExpectationKernel.firstSuccess_map_mean (tree.attemptKernel false hc budget hm K leafAttempts)
    tree.outputLabel attempts (fun result => test (result.getD fallback))
  change ((tree.attemptKernel false hc budget hm K leafAttempts).firstSuccess attempts).mean lifted =
    (mapped.firstSuccess attempts).mean (fun result => test (result.getD fallback)) at hMap
  change |(mapped.firstSuccess attempts).mean (fun result => test (result.getD fallback)) -
    (tree.projected.targetKernel budget hm).mean test| ≤ _ at hIdeal
  rw [← hMap] at hIdeal
  exact (abs_sub_le _ _ _).trans (add_le_add hNative hIdeal)

theorem output_mean_error_factor (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts attempts : ℕ)
    (fallback : Fin tree.projected.real.trueSize) (test : Fin tree.projected.real.trueSize → ℝ)
    (hTest : ∀ label, 0 ≤ test label ∧ test label ≤ 1) :
    |(fairBitKernel (attempts * tree.attemptBitBudget K leafAttempts)).mean
      (fun bits => test (tree.output hc budget hm K leafAttempts attempts fallback bits)) -
        (tree.projected.targetKernel budget hm).mean test| ≤
          (attempts : ℝ) * (tree.error K leafAttempts + 1 / (2 : ℝ) ^ K) +
            (1 - 1 / (tree.projected.factor : ℝ)) ^ attempts := by
  have he := tree.output_mean_error hc budget hm K leafAttempts attempts fallback test hTest
  exact he.trans (add_le_add (le_refl _) (tree.projected.idealFailure_factor_bound hc budget hm attempts))

theorem output_feasible (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts attempts : ℕ)
    (fallback : Fin tree.projected.real.trueSize)
    (hFallback : tree.projected.real.trueFamily.resource fallback ≤ (budget : ℝ))
    (bits : Fin (attempts * tree.attemptBitBudget K leafAttempts) → Bool) :
    tree.projected.real.trueFamily.resource (tree.output hc budget hm K leafAttempts attempts fallback bits) ≤ (budget : ℝ) := by
  unfold output
  cases hRecord : tree.rejection hc budget hm K leafAttempts attempts bits with
  | none => exact hFallback
  | some record =>
    have hResource := tree.rejection_feasible hc budget hm K leafAttempts attempts bits record hRecord
    have hReal : (tree.resource record : ℝ) ≤ (budget : ℝ) := by exact_mod_cast hResource
    rw [← tree.projected_resource record, tree.projected.resource_real] at hReal
    exact hReal

theorem output_event_error (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts attempts : ℕ)
    (fallback : Fin tree.projected.real.trueSize) (event : Set (Fin tree.projected.real.trueSize)) :
    |(fairBitKernel (attempts * tree.attemptBitBudget K leafAttempts)).mean
      (fun bits => if tree.output hc budget hm K leafAttempts attempts fallback bits ∈ event then 1 else 0) -
        (tree.projected.targetKernel budget hm).mean (fun label => if label ∈ event then 1 else 0)| ≤
          (attempts : ℝ) * (tree.error K leafAttempts + 1 / (2 : ℝ) ^ K) +
            (1 - 1 / (tree.projected.factor : ℝ)) ^ attempts :=
  tree.output_mean_error_factor hc budget hm K leafAttempts attempts fallback
    (fun label => if label ∈ event then 1 else 0) (fun label => by split_ifs <;> norm_num)

def nativeOutputLabel (tree : ProposalTree) (record : tree.Record) : Fin tree.projected.trueSize :=
  tree.projected.nativeTrueOutput (tree.toProjected record)

def nativeOutput (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts attempts : ℕ)
    (fallback : Fin tree.projected.trueSize)
    (bits : Fin (attempts * tree.attemptBitBudget K leafAttempts) → Bool) : Fin tree.projected.trueSize :=
  ((tree.rejection hc budget hm K leafAttempts attempts bits).map tree.nativeOutputLabel).getD fallback

theorem nativeOutput_eq (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts attempts : ℕ)
    (fallback : Fin tree.projected.trueSize)
    (bits : Fin (attempts * tree.attemptBitBudget K leafAttempts) → Bool) :
    (tree.nativeOutput hc budget hm K leafAttempts attempts fallback bits).cast tree.projected.real_trueSize.symm =
      tree.output hc budget hm K leafAttempts attempts (fallback.cast tree.projected.real_trueSize.symm) bits := by
  unfold nativeOutput output
  cases he : tree.rejection hc budget hm K leafAttempts attempts bits with
  | none => rfl
  | some record => exact tree.projected.nativeTrueOutput_eq (tree.toProjected record)

theorem nativeOutput_mean_error (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts attempts : ℕ)
    (fallback : Fin tree.projected.trueSize) (test : Fin tree.projected.real.trueSize → ℝ)
    (hTest : ∀ label, 0 ≤ test label ∧ test label ≤ 1) :
    |(fairBitKernel (attempts * tree.attemptBitBudget K leafAttempts)).mean
      (fun bits => test ((tree.nativeOutput hc budget hm K leafAttempts attempts fallback bits).cast tree.projected.real_trueSize.symm)) -
        (tree.projected.targetKernel budget hm).mean test| ≤
          (attempts : ℝ) * (tree.error K leafAttempts + 1 / (2 : ℝ) ^ K) +
            (1 - 1 / (tree.projected.factor : ℝ)) ^ attempts := by
  simp_rw [tree.nativeOutput_eq hc budget hm K leafAttempts attempts fallback]
  exact tree.output_mean_error_factor hc budget hm K leafAttempts attempts _ test hTest

theorem nativeOutput_feasible (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts attempts : ℕ)
    (fallback : Fin tree.projected.trueSize)
    (hFallback : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ))
    (bits : Fin (attempts * tree.attemptBitBudget K leafAttempts) → Bool) :
    tree.projected.real.trueFamily.resource
      ((tree.nativeOutput hc budget hm K leafAttempts attempts fallback bits).cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ) := by
  rw [tree.nativeOutput_eq]
  exact tree.output_feasible hc budget hm K leafAttempts attempts _ hFallback bits

end ProposalTree
end ImplicitLeafCounts
end Blotto
