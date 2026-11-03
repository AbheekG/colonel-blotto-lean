import Blotto.RationalProposalAttemptLaw

/-! Native capped rejection consumes one fixed finite attempt block per trial.
The first successful whole record is returned; otherwise failure is explicit.
The recursion has the exact first-success kernel law, without conditioning. -/

namespace Blotto
open scoped BigOperators Classical
namespace RationalWeightedGuideTree

def rejectionFinite (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified) (B : ℚ)
    (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K : ℕ) :
    (attempts : ℕ) → (Fin (attempts * tree.attemptBitBudget K) → Bool) → Option tree.Record
  | 0, _ => none
  | attempts + 1, bits =>
      let width := tree.attemptBitBudget K
      let seed : Fin (width + attempts * width) → Bool := fun j => bits (j.cast (by dsimp [width]; ring))
      match tree.attemptFinite hc B hm K (firstBitBlock width (attempts * width) seed) with
      | some record => some record
      | none => tree.rejectionFinite hc B hm K attempts (secondBitBlock width (attempts * width) seed)

theorem rejectionFinite_mean (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K attempts : ℕ)
    (f : Option tree.Record → ℝ) :
    (fairBitKernel (attempts * tree.attemptBitBudget K)).mean
      (fun bits => f (tree.rejectionFinite hc B hm K attempts bits)) =
      ((tree.attemptKernel true hc B hm K).firstSuccess attempts).mean f := by
  induction attempts with
  | zero =>
    simp only [rejectionFinite, BoundedExpectationKernel.firstSuccess, BoundedExpectationKernel.point]
    exact (fairBitKernel (0 * tree.attemptBitBudget K)).constant (f none)
  | succ attempts ih =>
    let width := tree.attemptBitBudget K
    have hSize : (attempts + 1) * width = width + attempts * width := by ring
    have hCast := fairBitKernel_cast (width + attempts * width) ((attempts + 1) * width) hSize.symm
      (fun bits => f (tree.rejectionFinite hc B hm K (attempts + 1) bits))
    apply hCast.symm.trans
    have hSplit := fairBitKernel_blocks width (attempts * width)
      (fun first rest => f (match tree.attemptFinite hc B hm K first with
        | some record => some record | none => tree.rejectionFinite hc B hm K attempts rest))
    apply hSplit.trans
    have hRest : ∀ result : Option tree.Record,
        (fairBitKernel (attempts * width)).mean (fun bits =>
          f (match result with | some record => some record | none => tree.rejectionFinite hc B hm K attempts bits)) =
        match result with
        | some record => f (some record)
        | none => ((tree.attemptKernel true hc B hm K).firstSuccess attempts).mean f := by
      intro result
      cases result with
      | none => exact ih
      | some record =>
        dsimp only
        exact (fairBitKernel _).constant _
    simp_rw [hRest]
    have hAttempt := tree.attemptFinite_mean hc B hm K (fun result =>
      match result with | some record => f (some record) | none => ((tree.attemptKernel true hc B hm K).firstSuccess attempts).mean f)
    apply hAttempt.trans
    have hOrder : (fun result : Option tree.Record => match result with
      | some record => f (some record) | none => ((tree.attemptKernel true hc B hm K).firstSuccess attempts).mean f) =
      (fun result => match result with
      | none => ((tree.attemptKernel true hc B hm K).firstSuccess attempts).mean f | some record => f (some record)) := by
      funext result; cases result <;> rfl
    rw [hOrder]
    conv_rhs => unfold BoundedExpectationKernel.firstSuccess
    change (tree.attemptKernel true hc B hm K).mean _ = (tree.attemptKernel true hc B hm K).mean _
    apply congrArg (tree.attemptKernel true hc B hm K).mean
    funext result
    cases result <;> rfl

theorem rejectionFinite_mean_error (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K attempts : ℕ)
    (f : Option tree.Record → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |(fairBitKernel (attempts * tree.attemptBitBudget K)).mean
      (fun bits => f (tree.rejectionFinite hc B hm K attempts bits)) -
      ((tree.attemptKernel false hc B hm K).firstSuccess attempts).mean f| ≤
        (attempts : ℝ) * (((tree.nodes : ℝ) + 1) * (1 / (2 : ℝ) ^ K)) := by
  rw [tree.rejectionFinite_mean]
  exact BoundedExpectationKernel.firstSuccess_close _ _ _ (by positivity)
    (tree.attemptKernel_error hc B hm K) attempts f hf

theorem rejectionFinite_feasible (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (hm : 0 < tree.real.trueFamily.prefixMass (B : ℝ)) (K attempts : ℕ)
    (bits : Fin (attempts * tree.attemptBitBudget K) → Bool) (record : tree.Record)
    (h : tree.rejectionFinite hc B hm K attempts bits = some record) : tree.resource record ≤ B := by
  induction attempts with
  | zero => cases h
  | succ attempts ih =>
    unfold rejectionFinite at h
    dsimp only at h
    split at h
    · rename_i record' he
      cases Option.some.inj h
      exact tree.attemptFinite_feasible hc B hm K _ record he
    · exact ih _ h

end RationalWeightedGuideTree
end Blotto
