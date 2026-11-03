import Blotto.ImplicitRecursiveProposalLaw
import Blotto.RationalRejectionOutputLaw
import Blotto.RationalRejectionFeasibility

/-! Root acceptance uses the original certified proposal importance after the
implicit record projection. Native proposal and coin blocks are independent;
bounded first success is followed by an explicit feasible fallback. The
certification is the retained lower orientation, never an upper-guide swap. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts
namespace ProposalTree

def acceptProbability (tree : ProposalTree) (budget : ℚ) (record : tree.Record) : ℚ :=
  tree.projected.acceptanceProbability budget (tree.toProjected record)

theorem acceptProbability_unit (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (record : tree.Record) :
    0 ≤ tree.acceptProbability budget record ∧ tree.acceptProbability budget record ≤ 1 :=
  tree.projected.acceptanceProbability_unit hc budget hm _

def attemptBitBudget (tree : ProposalTree) (K leafAttempts : ℕ) : ℕ := tree.bitBudget K leafAttempts + 3 * (1 + K)

def attempt (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts : ℕ)
    (bits : Fin (tree.attemptBitBudget K leafAttempts) → Bool) : Option tree.Record :=
  match tree.sample budget K leafAttempts (firstBitBlock (tree.bitBudget K leafAttempts) (3 * (1 + K)) bits) with
  | none => none
  | some record => ((rationalAcceptanceAttempt (tree.acceptProbability budget record)
      (tree.acceptProbability_unit hc budget hm record)).sample K
        (secondBitBlock (tree.bitBudget K leafAttempts) (3 * (1 + K)) bits)).map (fun _ => record)

noncomputable def attemptKernel (actual : Bool) (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts : ℕ) :
    BoundedExpectationKernel (Option tree.Record) :=
  if actual then (tree.kernel true budget K leafAttempts).bind
    (rationalAcceptanceKernel (tree.acceptProbability budget) (tree.acceptProbability_unit hc budget hm) K)
  else (tree.kernel false budget K leafAttempts).bind
    (acceptanceKernel (fun record => (tree.acceptProbability budget record : ℝ))
      (fun record => by exact_mod_cast tree.acceptProbability_unit hc budget hm record))

theorem attempt_mean (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts : ℕ) (f : Option tree.Record → ℝ) :
    (fairBitKernel (tree.attemptBitBudget K leafAttempts)).mean (fun bits => f (tree.attempt hc budget hm K leafAttempts bits)) =
      (tree.attemptKernel true hc budget hm K leafAttempts).mean f := by
  have he := fairBitKernel_blocks (tree.bitBudget K leafAttempts) (3 * (1 + K))
    (fun proposalBits coinBits => f (match tree.sample budget K leafAttempts proposalBits with
      | none => none
      | some record => ((rationalAcceptanceAttempt (tree.acceptProbability budget record)
          (tree.acceptProbability_unit hc budget hm record)).sample K coinBits).map (fun _ => record)))
  apply he.trans
  have hCoin : ∀ result : Option tree.Record,
      (fairBitKernel (3 * (1 + K))).mean (fun bits => f (match result with
        | none => none
        | some record => ((rationalAcceptanceAttempt (tree.acceptProbability budget record)
            (tree.acceptProbability_unit hc budget hm record)).sample K bits).map (fun _ => record))) =
      (rationalAcceptanceKernel (tree.acceptProbability budget) (tree.acceptProbability_unit hc budget hm) K result).mean f := by
    intro result
    cases result with
    | none => dsimp only [rationalAcceptanceKernel]; exact (fairBitKernel _).constant _
    | some record => rfl
  have hFunctions : (fun proposalBits : Fin (tree.bitBudget K leafAttempts) → Bool =>
      (fairBitKernel (3 * (1 + K))).mean (fun coinBits => f (match tree.sample budget K leafAttempts proposalBits with
      | none => none
      | some record => ((rationalAcceptanceAttempt (tree.acceptProbability budget record)
          (tree.acceptProbability_unit hc budget hm record)).sample K coinBits).map (fun _ => record)))) =
      (fun proposalBits => (rationalAcceptanceKernel (tree.acceptProbability budget)
        (tree.acceptProbability_unit hc budget hm) K (tree.sample budget K leafAttempts proposalBits)).mean f) := by
    funext proposalBits
    have he := hCoin (tree.sample budget K leafAttempts proposalBits)
    cases hr : tree.sample budget K leafAttempts proposalBits <;> simpa only [hr] using he
  rw [hFunctions]
  exact tree.sample_mean budget K leafAttempts (fun result =>
    (rationalAcceptanceKernel (tree.acceptProbability budget) (tree.acceptProbability_unit hc budget hm) K result).mean f)

theorem attemptKernel_error (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts : ℕ) :
    (tree.attemptKernel true hc budget hm K leafAttempts).Close (tree.attemptKernel false hc budget hm K leafAttempts)
      (tree.error K leafAttempts + 1 / (2 : ℝ) ^ K) := by
  have he := proposal_and_acceptance_error (tree.kernel true budget K leafAttempts) (tree.kernel false budget K leafAttempts)
    (tree.acceptProbability budget) (tree.acceptProbability_unit hc budget hm) _ (tree.kernel_error budget K leafAttempts) K
  exact he

theorem attempt_success (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts : ℕ)
    (bits : Fin (tree.attemptBitBudget K leafAttempts) → Bool) (record : tree.Record)
    (h : tree.attempt hc budget hm K leafAttempts bits = some record) :
    tree.sample budget K leafAttempts (firstBitBlock (tree.bitBudget K leafAttempts) (3 * (1 + K)) bits) = some record := by
  unfold attempt at h
  split at h
  · cases h
  · rename_i proposed hProposed
    cases hCoin : (rationalAcceptanceAttempt (tree.acceptProbability budget proposed)
      (tree.acceptProbability_unit hc budget hm proposed)).sample K
        (secondBitBlock (tree.bitBudget K leafAttempts) (3 * (1 + K)) bits) with
    | none => rw [hCoin] at h; cases h
    | some flag => rw [hCoin] at h; cases Option.some.inj h; exact hProposed

theorem attempt_feasible (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts : ℕ)
    (bits : Fin (tree.attemptBitBudget K leafAttempts) → Bool) (record : tree.Record)
    (h : tree.attempt hc budget hm K leafAttempts bits = some record) : tree.resource record ≤ budget :=
  tree.sample_feasible budget K leafAttempts _ record (tree.attempt_success hc budget hm K leafAttempts bits record h)

def rejection (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts : ℕ) :
    (attempts : ℕ) → (Fin (attempts * tree.attemptBitBudget K leafAttempts) → Bool) → Option tree.Record
  | 0, _ => none
  | attempts + 1, bits =>
    let width := tree.attemptBitBudget K leafAttempts
    let seed : Fin (width + attempts * width) → Bool := fun index => bits (index.cast (by dsimp only [width]; ring))
    match tree.attempt hc budget hm K leafAttempts (firstBitBlock width (attempts * width) seed) with
    | some record => some record
    | none => tree.rejection hc budget hm K leafAttempts attempts (secondBitBlock width (attempts * width) seed)

theorem rejection_mean (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts attempts : ℕ)
    (f : Option tree.Record → ℝ) :
    (fairBitKernel (attempts * tree.attemptBitBudget K leafAttempts)).mean
      (fun bits => f (tree.rejection hc budget hm K leafAttempts attempts bits)) =
        ((tree.attemptKernel true hc budget hm K leafAttempts).firstSuccess attempts).mean f := by
  induction attempts with
  | zero => simp only [rejection, BoundedExpectationKernel.firstSuccess, BoundedExpectationKernel.point]; exact (fairBitKernel _).constant _
  | succ attempts ih =>
    let width := tree.attemptBitBudget K leafAttempts
    have hSize : (attempts + 1) * width = width + attempts * width := by ring
    have hCast := fairBitKernel_cast (width + attempts * width) ((attempts + 1) * width) hSize.symm
      (fun bits => f (tree.rejection hc budget hm K leafAttempts (attempts + 1) bits))
    apply hCast.symm.trans
    have hSplit := fairBitKernel_blocks width (attempts * width) (fun first rest => f
      (match tree.attempt hc budget hm K leafAttempts first with
      | some record => some record | none => tree.rejection hc budget hm K leafAttempts attempts rest))
    apply hSplit.trans
    have hRest : ∀ result : Option tree.Record,
        (fairBitKernel (attempts * width)).mean (fun bits => f (match result with
          | some record => some record | none => tree.rejection hc budget hm K leafAttempts attempts bits)) =
        match result with | some record => f (some record) | none => ((tree.attemptKernel true hc budget hm K leafAttempts).firstSuccess attempts).mean f := by
      intro result
      cases result with
      | none => exact ih
      | some record => dsimp only; exact (fairBitKernel _).constant _
    simp_rw [hRest]
    have hAttempt := tree.attempt_mean hc budget hm K leafAttempts (fun result => match result with
      | some record => f (some record)
      | none => ((tree.attemptKernel true hc budget hm K leafAttempts).firstSuccess attempts).mean f)
    apply hAttempt.trans
    rw [BoundedExpectationKernel.firstSuccess_mean_recurrence]
    apply congrArg (tree.attemptKernel true hc budget hm K leafAttempts).mean
    funext result
    cases result <;> rfl

theorem rejection_mean_error (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts attempts : ℕ)
    (f : Option tree.Record → ℝ) (hf : ∀ record, 0 ≤ f record ∧ f record ≤ 1) :
    |(fairBitKernel (attempts * tree.attemptBitBudget K leafAttempts)).mean
      (fun bits => f (tree.rejection hc budget hm K leafAttempts attempts bits)) -
        ((tree.attemptKernel false hc budget hm K leafAttempts).firstSuccess attempts).mean f| ≤
          (attempts : ℝ) * (tree.error K leafAttempts + 1 / (2 : ℝ) ^ K) := by
  rw [rejection_mean]
  exact BoundedExpectationKernel.firstSuccess_close _ _ _ (by positivity [tree.error_nonnegative K leafAttempts])
    (tree.attemptKernel_error hc budget hm K leafAttempts) attempts f hf

theorem rejection_feasible (tree : ProposalTree) (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K leafAttempts attempts : ℕ)
    (bits : Fin (attempts * tree.attemptBitBudget K leafAttempts) → Bool) (record : tree.Record)
    (h : tree.rejection hc budget hm K leafAttempts attempts bits = some record) : tree.resource record ≤ budget := by
  induction attempts with
  | zero => cases h
  | succ attempts ih =>
    unfold rejection at h
    dsimp only at h
    split at h
    · rename_i found hf
      cases Option.some.inj h
      exact tree.attempt_feasible hc budget hm K leafAttempts _ _ hf
    · exact ih _ h

end ProposalTree
end ImplicitLeafCounts
end Blotto
