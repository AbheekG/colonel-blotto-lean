import Blotto.RationalProposalBlockSampler

/-! Direct finite-block native recursion realizes the actual independent
node kernel exactly. No output-support enumeration appears in the runtime. -/

namespace Blotto
open scoped BigOperators Classical
namespace RationalWeightedGuideTree

theorem sampleBlocks_mean (tree : RationalWeightedGuideTree) (B : ℚ) (K : ℕ)
    (f : Option tree.Record → ℝ) :
    (fairBitKernel (tree.totalBitBudget K)).mean (fun bits => f (tree.sampleBlocks B K bits)) =
      (tree.proposalKernel true B K).mean f := by
  induction tree generalizing B with
  | leaf family guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    change Option (Fin left.guideSize × right.Record × left.Record) → ℝ at f
    let root := 3 * (left.guideSize - 1 + K)
    have hSize : (fork guide gamma left right).totalBitBudget K =
        root + (right.totalBitBudget K + left.totalBitBudget K) := by dsimp [root, totalBitBudget]; omega
    have hCast := fairBitKernel_cast
      (root + (right.totalBitBudget K + left.totalBitBudget K))
      ((fork guide gamma left right).totalBitBudget K) hSize.symm
      (fun bits => f ((fork guide gamma left right).sampleBlocks B K bits))
    apply hCast.symm.trans
    change (fairBitKernel (root + (right.totalBitBudget K + left.totalBitBudget K))).mean
      (fun bits => f ((fork guide gamma left right).sampleBlocks B K
        (fun j => bits (j.cast hSize)))) = _
    have hRun : ∀ bits : Fin (root + (right.totalBitBudget K + left.totalBitBudget K)) → Bool,
        (fork guide gamma left right).sampleBlocks B K (fun j => bits (j.cast hSize)) =
        match left.guide.syntheticSample right.guide B K
          (finiteBitReader (firstBitBlock root (right.totalBitBudget K + left.totalBitBudget K) bits)) with
        | none => none
        | some i =>
          match right.sampleBlocks (B - left.guide.resource i) K
            (firstBitBlock (right.totalBitBudget K) (left.totalBitBudget K)
              (secondBitBlock root (right.totalBitBudget K + left.totalBitBudget K) bits)) with
          | none => none
          | some r => (left.sampleBlocks (B - right.resource r) K
              (secondBitBlock (right.totalBitBudget K) (left.totalBitBudget K)
                (secondBitBlock root (right.totalBitBudget K + left.totalBitBudget K) bits))).map (fun l => (i, r, l)) := by
      intro bits
      rfl
    simp_rw [hRun]
    have hSplit := fairBitKernel_blocks root (right.totalBitBudget K + left.totalBitBudget K)
      (fun first rest => f (match left.guide.syntheticSample right.guide B K (finiteBitReader first) with
        | none => none
        | some i => match right.sampleBlocks (B - left.guide.resource i) K
            (firstBitBlock (right.totalBitBudget K) (left.totalBitBudget K) rest) with
          | none => none
          | some r => (left.sampleBlocks (B - right.resource r) K
              (secondBitBlock (right.totalBitBudget K) (left.totalBitBudget K) rest)).map (fun l => (i, r, l))))
    apply hSplit.trans
    have hRest : ∀ selected : Option (Fin left.guideSize),
        (fairBitKernel (right.totalBitBudget K + left.totalBitBudget K)).mean (fun bits =>
          f (match selected with
          | none => none
          | some i => match right.sampleBlocks (B - left.guide.resource i) K
              (firstBitBlock (right.totalBitBudget K) (left.totalBitBudget K) bits) with
            | none => none
            | some r => (left.sampleBlocks (B - right.resource r) K
                (secondBitBlock (right.totalBitBudget K) (left.totalBitBudget K) bits)).map (fun l => (i, r, l)))) =
        (match selected with
        | none => BoundedExpectationKernel.point none
        | some i => (right.proposalKernel true (B - left.guide.resource i) K).bind (fun r =>
            match r with
            | none => BoundedExpectationKernel.point none
            | some r => (left.proposalKernel true (B - right.resource r) K).map (fun l => l.map (fun l => (i, r, l))))).mean f := by
      intro selected
      cases selected with
      | none =>
        dsimp only
        exact (fairBitKernel _).constant _
      | some i =>
        dsimp only
        have hSplitChildren := fairBitKernel_blocks (right.totalBitBudget K) (left.totalBitBudget K)
          (fun rightBits leftBits => f (match right.sampleBlocks (B - left.guide.resource i) K rightBits with
            | none => none
            | some r => (left.sampleBlocks (B - right.resource r) K leftBits).map (fun l => (i, r, l))))
        apply hSplitChildren.trans
        have hLeft : ∀ r : Option right.Record,
            (fairBitKernel (left.totalBitBudget K)).mean
              (fun bits => f (match r with | none => none | some r => (left.sampleBlocks (B - right.resource r) K bits).map (fun l => (i, r, l)))) =
            (match r with
            | none => BoundedExpectationKernel.point none
            | some r => (left.proposalKernel true (B - right.resource r) K).map (fun l => l.map (fun l => (i, r, l)))).mean f := by
          intro r
          cases r with
          | none =>
            dsimp only
            exact (fairBitKernel _).constant _
          | some r =>
            dsimp only [BoundedExpectationKernel.map, BoundedExpectationKernel.bind, BoundedExpectationKernel.point]
            exact ihL (B - right.resource r) (fun x => f (x.map (fun l => (i, r, l))))
        simp_rw [hLeft]
        exact ihR (B - left.guide.resource i) (fun result =>
          (match result with
          | none => BoundedExpectationKernel.point none
          | some r => (left.proposalKernel true (B - right.resource r) K).map (fun l => l.map (fun l => (i, r, l)))).mean f)
    simp_rw [hRest]
    rfl

end RationalWeightedGuideTree
end Blotto
