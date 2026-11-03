import Blotto.RationalProposalFiniteLaw
import Blotto.RationalAcceptanceKernel
import Blotto.RejectionExpectationKernel

/-! Certified rational proposal importance produces a normalized acceptance
coin on every record, including impossible records. Native finite proposal and
coin blocks compose into one complete attempt with an unconditional error. -/

namespace Blotto
open scoped BigOperators Classical
namespace RationalWeightedGuideTree

def acceptanceBound (tree : RationalWeightedGuideTree) (B : ℚ) : ℚ := tree.guidePrefix B * tree.factor

theorem acceptanceBound_positive (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) : 0 < tree.acceptanceBound B := by
  have hg := (tree.real.prefix_positive_iff hc (B : ℝ)).mpr hm
  have hf : 0 < tree.real.factor := by linarith [tree.real.factor_ge_one hc]
  rw [← tree.guidePrefix_real] at hg
  rw [← tree.factor_real] at hf
  have hgq : 0 < tree.guidePrefix B := by exact_mod_cast hg
  have hfq : 0 < tree.factor := by exact_mod_cast hf
  exact mul_pos hgq hfq

theorem importance_bound_rational (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (record : tree.Record) : tree.importance B record ≤ tree.acceptanceBound B := by
  have he := tree.real.proposalImportance_bound hc (B : ℝ) (tree.recordReal record)
  rw [← tree.importance_real, ← tree.factor_real, ← tree.guidePrefix_real] at he
  have hq : tree.importance B record ≤ tree.factor * tree.guidePrefix B := by exact_mod_cast he
  simpa only [acceptanceBound, mul_comm] using hq

def acceptanceProbability (tree : RationalWeightedGuideTree) (B : ℚ) (record : tree.Record) : ℚ :=
  tree.importance B record / tree.acceptanceBound B

theorem acceptanceProbability_unit (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (record : tree.Record) :
    0 ≤ tree.acceptanceProbability B record ∧ tree.acceptanceProbability B record ≤ 1 := by
  have hb := tree.acceptanceBound_positive hc B hm
  have hn : 0 ≤ tree.importance B record := by
    have he := tree.real.proposalImportance_nonnegative (B : ℝ) (tree.recordReal record)
    rw [← tree.importance_real] at he
    exact_mod_cast he
  exact ⟨div_nonneg hn hb.le, (div_le_one hb).mpr (tree.importance_bound_rational hc B record)⟩

def attemptBitBudget (tree : RationalWeightedGuideTree) (K : ℕ) : ℕ := tree.totalBitBudget K + 3 * (1 + K)

def attemptFinite (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified) (B : ℚ)
    (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K : ℕ)
    (bits : Fin (tree.attemptBitBudget K) → Bool) : Option tree.Record :=
  let proposal := tree.sampleFinite B K (firstBitBlock (tree.totalBitBudget K) (3 * (1 + K)) bits)
  match proposal with
  | none => none
  | some record =>
      ((rationalAcceptanceAttempt (tree.acceptanceProbability B record)
        (tree.acceptanceProbability_unit hc B hm record)).sample K
          (secondBitBlock (tree.totalBitBudget K) (3 * (1 + K)) bits)).map (fun _ => record)

noncomputable def attemptKernel (actual : Bool) (tree : RationalWeightedGuideTree)
    (hc : tree.real.LowerCertified) (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K : ℕ) :
    BoundedExpectationKernel (Option tree.Record) :=
  if actual then (tree.proposalKernel true B K).bind
    (rationalAcceptanceKernel (tree.acceptanceProbability B) (tree.acceptanceProbability_unit hc B hm) K)
  else (tree.proposalKernel false B K).bind
    (acceptanceKernel (fun record => (tree.acceptanceProbability B record : ℝ))
      (fun record => by exact_mod_cast tree.acceptanceProbability_unit hc B hm record))

theorem attemptKernel_error (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K : ℕ) :
    (tree.attemptKernel true hc B hm K).Close (tree.attemptKernel false hc B hm K)
      (((tree.nodes : ℝ) + 1) * (1 / (2 : ℝ) ^ K)) := by
  have he := proposal_and_acceptance_error (tree.proposalKernel true B K) (tree.proposalKernel false B K)
    (tree.acceptanceProbability B) (tree.acceptanceProbability_unit hc B hm)
    _ (tree.proposalKernel_error B K) K
  intro f hf
  have ht := he f hf
  simpa [attemptKernel, add_mul, one_mul] using ht

end RationalWeightedGuideTree
end Blotto
