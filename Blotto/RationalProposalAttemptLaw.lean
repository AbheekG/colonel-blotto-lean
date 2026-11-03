import Blotto.RationalProposalAcceptance

/-! One native complete rejection attempt uses consecutive proposal and coin
blocks. Its exact independent kernel identity includes bypassing the coin on
proposal failure, and preserves the complete sampled record. -/

namespace Blotto
open scoped BigOperators Classical
namespace RationalWeightedGuideTree

theorem attemptFinite_mean (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K : ℕ)
    (f : Option tree.Record → ℝ) :
    (fairBitKernel (tree.attemptBitBudget K)).mean (fun bits => f (tree.attemptFinite hc B hm K bits)) =
      (tree.attemptKernel true hc B hm K).mean f := by
  have he := fairBitKernel_blocks (tree.totalBitBudget K) (3 * (1 + K))
    (fun proposalBits coinBits => f (match tree.sampleFinite B K proposalBits with
      | none => none
      | some record => ((rationalAcceptanceAttempt (tree.acceptanceProbability B record)
          (tree.acceptanceProbability_unit hc B hm record)).sample K coinBits).map (fun _ => record)))
  apply he.trans
  have hCoin : ∀ result : Option tree.Record,
      (fairBitKernel (3 * (1 + K))).mean (fun bits => f (match result with
        | none => none
        | some record => ((rationalAcceptanceAttempt (tree.acceptanceProbability B record)
            (tree.acceptanceProbability_unit hc B hm record)).sample K bits).map (fun _ => record))) =
      (rationalAcceptanceKernel (tree.acceptanceProbability B) (tree.acceptanceProbability_unit hc B hm) K result).mean f := by
    intro result
    cases result with
    | none =>
      dsimp only [rationalAcceptanceKernel]
      exact (fairBitKernel _).constant _
    | some record => rfl
  change (fairBitKernel (tree.totalBitBudget K)).mean (fun proposalBits =>
    (fairBitKernel (3 * (1 + K))).mean (fun coinBits => f (match tree.sampleFinite B K proposalBits with
    | none => none
    | some record => ((rationalAcceptanceAttempt (tree.acceptanceProbability B record)
        (tree.acceptanceProbability_unit hc B hm record)).sample K coinBits).map (fun _ => record)))) = _
  have hFunctions : (fun proposalBits : Fin (tree.totalBitBudget K) → Bool =>
      (fairBitKernel (3 * (1 + K))).mean (fun coinBits => f (match tree.sampleFinite B K proposalBits with
      | none => none
      | some record => ((rationalAcceptanceAttempt (tree.acceptanceProbability B record)
          (tree.acceptanceProbability_unit hc B hm record)).sample K coinBits).map (fun _ => record)))) =
      (fun proposalBits => (rationalAcceptanceKernel (tree.acceptanceProbability B)
        (tree.acceptanceProbability_unit hc B hm) K (tree.sampleFinite B K proposalBits)).mean f) := by
    funext proposalBits
    have he := hCoin (tree.sampleFinite B K proposalBits)
    cases hr : tree.sampleFinite B K proposalBits <;> simpa only [hr] using he
  rw [hFunctions]
  exact tree.sampleFinite_mean B K (fun result =>
    (rationalAcceptanceKernel (tree.acceptanceProbability B) (tree.acceptanceProbability_unit hc B hm) K result).mean f)

theorem attemptFinite_mean_error (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K : ℕ)
    (f : Option tree.Record → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |(fairBitKernel (tree.attemptBitBudget K)).mean (fun bits => f (tree.attemptFinite hc B hm K bits)) -
      (tree.attemptKernel false hc B hm K).mean f| ≤ ((tree.nodes : ℝ) + 1) * (1 / (2 : ℝ) ^ K) := by
  rw [tree.attemptFinite_mean]
  exact tree.attemptKernel_error hc B hm K f hf

theorem attemptFinite_success_record (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K : ℕ)
    (bits : Fin (tree.attemptBitBudget K) → Bool) (record : tree.Record)
    (h : tree.attemptFinite hc B hm K bits = some record) :
    tree.sampleFinite B K (firstBitBlock (tree.totalBitBudget K) (3 * (1 + K)) bits) = some record := by
  unfold attemptFinite at h
  dsimp only at h
  split at h
  · cases h
  · rename_i proposed hp
    cases he : (rationalAcceptanceAttempt (tree.acceptanceProbability B proposed)
        (tree.acceptanceProbability_unit hc B hm proposed)).sample K
          (secondBitBlock (tree.totalBitBudget K) (3 * (1 + K)) bits) with
    | none => rw [he] at h; cases h
    | some flag =>
      rw [he] at h
      cases Option.some.inj h
      exact hp

theorem attemptFinite_feasible (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K : ℕ)
    (bits : Fin (tree.attemptBitBudget K) → Bool) (record : tree.Record)
    (h : tree.attemptFinite hc B hm K bits = some record) : tree.resource record ≤ B :=
  tree.sampleFinite_feasible hc B K _ record (tree.attemptFinite_success_record hc B hm K bits record h)

end RationalWeightedGuideTree
end Blotto
