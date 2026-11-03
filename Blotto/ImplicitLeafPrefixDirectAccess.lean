import Blotto.ImplicitLeafDirectAccess

/-! Actual proposal importance uses block-prefix mass, not a numerical-label
sum. Stored direct caps preserve the exact original conditional normalizer,
including empty prefixes. -/

namespace Blotto.ImplicitLeafCounts.LeafAccess

def massPrefix {leaf : ProposalLeaf} (access : LeafAccess leaf) (budget : ℚ) : ℚ :=
  prefixMass leaf.blocks (access.cap budget)

theorem massPrefix_eq {leaf : ProposalLeaf} (access : LeafAccess leaf) (budget : ℚ) :
    access.massPrefix budget = leaf.family.prefixMass budget := by
  unfold massPrefix
  rw [access.cap_eq]
  exact (decodedFamily_prefixMass leaf.cap leaf.blocks leaf.partition
    (fun block hb => (leaf.positive block hb).le) leaf.decode leaf.monotone budget).symm

end Blotto.ImplicitLeafCounts.LeafAccess
