import Blotto.RationalProposalFiniteSeeds
import Blotto.FairBitKernelBlocks
import Blotto.RationalRecursiveProposalKernel

/-! Direct consecutive-block recursion has exactly the independent node-kernel
law. Each subtree receives its fixed finite block, even when an earlier choice
fails. The address-list sampler refinement remains a separate equality. -/

namespace Blotto
open scoped BigOperators
namespace RationalWeightedGuideTree

def sampleBlocks : (tree : RationalWeightedGuideTree) → (B : ℚ) → (K : ℕ) →
    (Fin (tree.totalBitBudget K) → Bool) → Option tree.Record
  | .leaf family _ _, B, K, bits => family.conditionalSample B K (finiteBitReader bits)
  | .fork _ _ left right, B, K, bits =>
      let root := 3 * (left.guideSize - 1 + K)
      let first := firstBitBlock root (right.totalBitBudget K + left.totalBitBudget K)
        (fun j => bits (j.cast (by simp only [totalBitBudget]; omega)))
      let rest := secondBitBlock root (right.totalBitBudget K + left.totalBitBudget K)
        (fun j => bits (j.cast (by simp only [totalBitBudget]; omega)))
      let rightBits := firstBitBlock (right.totalBitBudget K) (left.totalBitBudget K) rest
      let leftBits := secondBitBlock (right.totalBitBudget K) (left.totalBitBudget K) rest
      match left.guide.syntheticSample right.guide B K (finiteBitReader first) with
      | none => none
      | some i =>
        match right.sampleBlocks (B - left.guide.resource i) K rightBits with
        | none => none
        | some r => (left.sampleBlocks (B - right.resource r) K leftBits).map (fun l => (i, r, l))

end RationalWeightedGuideTree
end Blotto
