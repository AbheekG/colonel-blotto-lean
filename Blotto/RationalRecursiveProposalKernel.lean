import Blotto.TotalPositiveChoiceKernel
import Blotto.RationalRecursiveProposalSampler

/-! Recursive actual block-kernel semantics uses independent fresh local
blocks; ideal semantics uses normalized rational choices. Bounded test errors
compose with one allowance per tree node. Equality to the flattened seed runner
is a separate finite-product layout proof, not asserted by this kernel theorem. -/

namespace Blotto
open scoped BigOperators Classical
namespace RationalWeightedGuideTree

def leafWeights {n : ℕ} (family : RationalWeightedFamily n) (B : ℚ) : Fin n → ℚ :=
  fun i => if family.resource i ≤ B then family.mass i else 0

theorem leafWeights_nonnegative {n : ℕ} (family : RationalWeightedFamily n) (B : ℚ) :
    ∀ i, 0 ≤ leafWeights family B i := by
  intro i
  unfold leafWeights
  split_ifs
  · exact family.mass_nonnegative i
  · exact le_rfl

def forkWeights (left right : RationalWeightedGuideTree) (B : ℚ) : Fin left.guideSize → ℚ :=
  fun i => left.guide.mass i * right.guidePrefix (B - left.guide.resource i)

theorem forkWeights_nonnegative (left right : RationalWeightedGuideTree) (B : ℚ) :
    ∀ i, 0 ≤ forkWeights left right B i := fun i =>
  mul_nonneg (left.guide.mass_nonnegative i) (right.guide.prefixMass_nonnegative _)

noncomputable def proposalKernel (actual : Bool) : (tree : RationalWeightedGuideTree) → ℚ → ℕ →
    BoundedExpectationKernel (Option tree.Record)
  | .leaf family _ _, B, K =>
      if actual then positiveChoiceKernel (leafWeights family B) (leafWeights_nonnegative family B) K
      else totalNormalizedKernel (leafWeights family B) (leafWeights_nonnegative family B)
  | .fork _ _ left right, B, K =>
      let choice := if actual then positiveChoiceKernel (forkWeights left right B) (forkWeights_nonnegative left right B) K
        else totalNormalizedKernel (forkWeights left right B) (forkWeights_nonnegative left right B)
      choice.bind (fun selected =>
        match selected with
        | none => BoundedExpectationKernel.point none
        | some i => (right.proposalKernel actual (B - left.guide.resource i) K).bind (fun r =>
            match r with
            | none => BoundedExpectationKernel.point none
            | some r => (left.proposalKernel actual (B - right.resource r) K).map (fun l =>
                l.map (fun l => (i, r, l)))))

theorem proposalKernel_error (tree : RationalWeightedGuideTree) (B : ℚ) (K : ℕ) :
    (tree.proposalKernel true B K).Close (tree.proposalKernel false B K)
      ((tree.nodes : ℝ) * (1 / (2 : ℝ) ^ K)) := by
  induction tree generalizing B with
  | leaf family guide gamma =>
    intro f hf
    have he := positiveChoiceKernel_total_close (leafWeights family B) (leafWeights_nonnegative family B) K f hf
    simpa [proposalKernel, Bool.true_eq_false, Bool.false_eq_true, ite_true, ite_false, nodes, Nat.cast_one, one_mul, Record, BoundedExpectationKernel.bind, BoundedExpectationKernel.map, BoundedExpectationKernel.point] using he
  | fork guide gamma left right ihL ihR =>
    have hChoice := positiveChoiceKernel_total_close (forkWeights left right B) (forkWeights_nonnegative left right B) K
    have hNext : ∀ selected : Option (Fin left.guideSize),
        (match selected with
        | none => BoundedExpectationKernel.point (none : Option (Fin left.guideSize × right.Record × left.Record))
        | some i => (right.proposalKernel true (B - left.guide.resource i) K).bind (fun r =>
            match r with
            | none => BoundedExpectationKernel.point none
            | some r => (left.proposalKernel true (B - right.resource r) K).map (fun l => l.map (fun l => (i, r, l))))).Close
        (match selected with
        | none => BoundedExpectationKernel.point none
        | some i => (right.proposalKernel false (B - left.guide.resource i) K).bind (fun r =>
            match r with
            | none => BoundedExpectationKernel.point none
            | some r => (left.proposalKernel false (B - right.resource r) K).map (fun l => l.map (fun l => (i, r, l)))))
        (((right.nodes : ℝ) + left.nodes) * (1 / (2 : ℝ) ^ K)) := by
      intro selected
      cases selected with
      | none => intro f _hf; simp only [sub_self, abs_zero]; positivity
      | some i =>
        have hContinuation : ∀ r : Option right.Record,
            (match r with
            | none => BoundedExpectationKernel.point (none : Option (Fin left.guideSize × right.Record × left.Record))
            | some r => (left.proposalKernel true (B - right.resource r) K).map (fun l => l.map (fun l => (i, r, l)))).Close
            (match r with
            | none => BoundedExpectationKernel.point none
            | some r => (left.proposalKernel false (B - right.resource r) K).map (fun l => l.map (fun l => (i, r, l))))
              ((left.nodes : ℝ) * (1 / (2 : ℝ) ^ K)) := by
          intro r
          cases r with
          | none => intro f _hf; simp only [sub_self, abs_zero]; positivity
          | some r => exact BoundedExpectationKernel.map_close _ _ _ _ (ihL _)
        have he := BoundedExpectationKernel.bind_close
          (right.proposalKernel true (B - left.guide.resource i) K)
          (right.proposalKernel false (B - left.guide.resource i) K) _ _
          ((right.nodes : ℝ) * (1 / (2 : ℝ) ^ K)) ((left.nodes : ℝ) * (1 / (2 : ℝ) ^ K))
          (ihR (B - left.guide.resource i)) hContinuation
        convert he using 1
        ring
    have he := BoundedExpectationKernel.bind_close _ _ _ _ _ _ hChoice hNext
    intro f hf
    have hTest := he f hf
    simpa [proposalKernel, ite_true, Bool.false_eq_true, ite_false, nodes, Nat.cast_add, Nat.cast_one,
      add_mul, one_mul, add_assoc, add_comm, add_left_comm, Record, BoundedExpectationKernel.bind, BoundedExpectationKernel.map, BoundedExpectationKernel.point] using hTest

end RationalWeightedGuideTree
end Blotto
