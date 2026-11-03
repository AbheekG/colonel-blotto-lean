import Blotto.ImplicitRecursiveProposal
import Blotto.RationalProposalIdealKernelLaw

/-! The implicit callback tree has exactly the original labelled ideal proposal
law after its recursive record projection. Existing positive-path probability
and importance arguments can therefore be reused under their original guide
certification hypotheses; no upper/lower orientation is exchanged here. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts
namespace ProposalTree

def fromProjected : (tree : ProposalTree) → tree.projected.Record → tree.Record
  | .leaf _ _ _, record => record
  | .fork _ _ left right, record => (record.1, right.fromProjected record.2.1, left.fromProjected record.2.2)

theorem to_fromProjected (tree : ProposalTree) (record : tree.projected.Record) :
    tree.toProjected (tree.fromProjected record) = record := by
  induction tree with
  | leaf data guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    change (record.1, right.toProjected (right.fromProjected record.2.1), left.toProjected (left.fromProjected record.2.2)) = record
    rw [ihL, ihR]
    exact Prod.eta _

theorem from_toProjected (tree : ProposalTree) (record : tree.Record) :
    tree.fromProjected (tree.toProjected record) = record := by
  induction tree with
  | leaf data guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    change (record.1, right.fromProjected (right.toProjected record.2.1), left.fromProjected (left.toProjected record.2.2)) = record
    rw [ihL, ihR]
    exact Prod.eta _

def recordEquiv (tree : ProposalTree) : tree.Record ≃ tree.projected.Record where
  toFun := tree.toProjected
  invFun := tree.fromProjected
  left_inv := tree.from_toProjected
  right_inv := tree.to_fromProjected

theorem ideal_kernel_projected (tree : ProposalTree) (budget : ℚ) (K attempts : ℕ)
    (test : Option tree.projected.Record → ℝ) :
    (tree.kernel false budget K attempts).mean (fun record => test (record.map tree.toProjected)) =
      (tree.projected.proposalKernel false budget K).mean test := by
  induction tree generalizing budget with
  | leaf data guide gamma =>
    change Option (Fin (data.cap + 1)) → ℝ at test
    change (data.idealKernel budget).mean (fun record => test (record.map (fun code => code))) = (data.idealKernel budget).mean test
    have he : (fun record : Option (Fin (data.cap + 1)) => test (record.map (leaf data guide gamma).toProjected)) = test := by
      funext record
      cases record <;> rfl
    exact congrArg (data.idealKernel budget).mean he
  | fork guide gamma left right ihL ihR =>
    change Option (Fin left.projected.guideSize × right.projected.Record × left.projected.Record) → ℝ at test
    have hMap : (fork guide gamma left right).toProjected =
        (fun record : Fin left.projected.guideSize × right.Record × left.Record =>
          (record.1, right.toProjected record.2.1, left.toProjected record.2.2)) := rfl
    rw [hMap]
    change (totalNormalizedKernel (RationalWeightedGuideTree.forkWeights left.projected right.projected budget) _).mean
      (fun selected => (match selected with
        | none => BoundedExpectationKernel.point none
        | some i => (right.kernel false (budget - left.projected.guide.resource i) K attempts).bind (fun r => match r with
          | none => BoundedExpectationKernel.point none
          | some r => (left.kernel false (budget - right.resource r) K attempts).map (fun l => l.map (fun l => (i, r, l))))).mean
        (fun record => test (record.map (fun record : Fin left.projected.guideSize × right.Record × left.Record =>
          (record.1, right.toProjected record.2.1, left.toProjected record.2.2))))) = _
    apply congrArg (totalNormalizedKernel (RationalWeightedGuideTree.forkWeights left.projected right.projected budget)
      (RationalWeightedGuideTree.forkWeights_nonnegative left.projected right.projected budget)).mean
    funext selected
    cases selected with
    | none => rfl
    | some i =>
      dsimp only [BoundedExpectationKernel.bind]
      have hLeft : ∀ r : Option right.Record,
          (match r with
          | none => BoundedExpectationKernel.point none
          | some r => (left.kernel false (budget - right.resource r) K attempts).map (fun l => l.map (fun l => (i, r, l)))).mean
            (fun record => test (record.map (fun record : Fin left.projected.guideSize × right.Record × left.Record =>
              (record.1, right.toProjected record.2.1, left.toProjected record.2.2)))) =
          (match r.map right.toProjected with
          | none => BoundedExpectationKernel.point none
          | some r => (left.projected.proposalKernel false (budget - right.projected.resource r) K).map
              (fun l => l.map (fun l => (i, r, l)))).mean test := by
        intro r
        cases r with
        | none => rfl
        | some r =>
          have he := ihL (budget - right.resource r)
            (fun l => test (l.map (fun l => (i, right.toProjected r, l))))
          dsimp only [Option.map, BoundedExpectationKernel.map, BoundedExpectationKernel.bind, BoundedExpectationKernel.point]
          rw [right.projected_resource r]
          have hTest : (fun record : Option left.Record =>
              test ((record.map (fun l => (i, r, l))).map
                (fun record : Fin left.projected.guideSize × right.Record × left.Record =>
                  (record.1, right.toProjected record.2.1, left.toProjected record.2.2)))) =
              fun record => test ((record.map left.toProjected).map (fun l => (i, right.toProjected r, l))) := by
            funext record
            cases record <;> rfl
          apply Eq.trans _ he
          apply congrArg (left.kernel false (budget - right.resource r) K attempts).mean
          funext record
          cases record <;> rfl
      simp_rw [hLeft]
      convert ihR (budget - left.projected.guide.resource i)
        (fun r => (match r with
          | none => BoundedExpectationKernel.point none
          | some r => (left.projected.proposalKernel false (budget - right.projected.resource r) K).map
              (fun l => l.map (fun l => (i, r, l)))).mean test) using 1
      apply congrArg (right.projected.proposalKernel false (budget - left.projected.guide.resource i) K).mean
      funext record
      cases record <;> rfl

theorem sample_projected_mean_error (tree : ProposalTree) (budget : ℚ) (K attempts : ℕ)
    (test : Option tree.projected.Record → ℝ) (hTest : ∀ record, 0 ≤ test record ∧ test record ≤ 1) :
    |(fairBitKernel (tree.bitBudget K attempts)).mean
      (fun bits => test ((tree.sample budget K attempts bits).map tree.toProjected)) -
      (tree.projected.proposalKernel false budget K).mean test| ≤ tree.error K attempts := by
  have he := tree.sample_mean_error budget K attempts (fun record => test (record.map tree.toProjected)) (fun record => hTest _)
  rw [tree.ideal_kernel_projected budget K attempts test] at he
  exact he

theorem sample_projected_probability_mean_error (tree : ProposalTree)
    (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (K attempts : ℕ)
    (test : Option tree.projected.Record → ℝ) (hTest : ∀ record, 0 ≤ test record ∧ test record ≤ 1) :
    |(fairBitKernel (tree.bitBudget K attempts)).mean
      (fun bits => test ((tree.sample budget K attempts bits).map tree.toProjected)) -
      (∑ record : tree.projected.Record, (tree.projected.probability budget record : ℝ) * test (some record))| ≤
        tree.error K attempts := by
  have he := tree.sample_projected_mean_error budget K attempts test hTest
  rw [tree.projected.proposalKernel_ideal_mean hc budget K hm test] at he
  exact he

end ProposalTree
end ImplicitLeafCounts
end Blotto
