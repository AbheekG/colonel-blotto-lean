import Blotto.ImplicitRecursiveSchedule

/-! Exact fixed-seed storage for the actual implicit-leaf recursive sampler.
Budgets sum stored block counts and guide sizes, rather than leaf label counts.
Bounds are derived from explicit local structural caps; deriving every retained
source guide cap and complete adaptive trainer costs remains separate. -/

namespace Blotto.ImplicitLeafCounts.ProposalTree

def leaves : ProposalTree → ℕ
  | .leaf _ _ _ => 1
  | .fork _ _ left right => left.leaves + right.leaves

def forks : ProposalTree → ℕ
  | .leaf _ _ _ => 0
  | .fork _ _ left right => 1 + left.forks + right.forks

def leafBlocks : ProposalTree → ℕ
  | .leaf data _ _ => data.blocks.length - 1
  | .fork _ _ left right => left.leafBlocks + right.leafBlocks

def leafWidths : ProposalTree → ℕ
  | .leaf data _ _ => offsetWidth data.cap
  | .fork _ _ left right => left.leafWidths + right.leafWidths

def forkChoices : ProposalTree → ℕ
  | .leaf _ _ _ => 0
  | .fork _ _ left right => left.projected.guideSize - 1 + left.forkChoices + right.forkChoices

theorem nodes_eq (tree : ProposalTree) : tree.projected.nodes = tree.leaves + tree.forks := by
  induction tree with
  | leaf data guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    simp only [projected, RationalWeightedGuideTree.nodes, leaves, forks, ihL, ihR]
    omega

theorem forks_add_one (tree : ProposalTree) : tree.forks + 1 = tree.leaves := by
  induction tree with
  | leaf data guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    simp only [leaves, forks]
    omega

theorem bitBudget_sum (tree : ProposalTree) (K attempts : ℕ) :
    tree.bitBudget K attempts =
      3 * (tree.leafBlocks + tree.forkChoices) + 3 * K * (tree.leaves + tree.forks) + attempts * tree.leafWidths := by
  induction tree with
  | leaf data guide gamma =>
    simp only [bitBudget, ProposalLeaf.bitBudget, prefixSampleBitBudget, leafBlocks, forkChoices,
      leaves, forks, leafWidths]
    ring
  | fork guide gamma left right ihL ihR =>
    simp only [bitBudget, leafBlocks, forkChoices, leaves, forks, leafWidths, ihL, ihR]
    ring

def StructuralCaps (blocks width guideSize : ℕ) : ProposalTree → Prop
  | .leaf data _ _ => data.blocks.length - 1 ≤ blocks ∧ offsetWidth data.cap ≤ width
  | .fork _ _ left right => left.projected.guideSize - 1 ≤ guideSize ∧
      left.StructuralCaps blocks width guideSize ∧ right.StructuralCaps blocks width guideSize

theorem structural_sum_caps (tree : ProposalTree) (blocks width guideSize : ℕ)
    (h : tree.StructuralCaps blocks width guideSize) :
    tree.leafBlocks ≤ tree.leaves * blocks ∧ tree.leafWidths ≤ tree.leaves * width ∧
      tree.forkChoices ≤ tree.forks * guideSize := by
  induction tree with
  | leaf data guide gamma =>
    simpa only [leafBlocks, leafWidths, forkChoices, leaves, forks, Nat.one_mul, Nat.zero_mul] using
      And.intro h.1 (And.intro h.2 (Nat.zero_le _))
  | fork guide gamma left right ihL ihR =>
    have hl := ihL h.2.1
    have hr := ihR h.2.2
    simp only [leafBlocks, leafWidths, forkChoices, leaves, forks]
    constructor
    · nlinarith [hl.1, hr.1]
    · constructor <;> nlinarith [hl.2.1, hr.2.1, hl.2.2, hr.2.2, h.1]

theorem bitBudget_structural_bound (tree : ProposalTree) (blocks width guideSize K attempts : ℕ)
    (h : tree.StructuralCaps blocks width guideSize) :
    tree.bitBudget K attempts ≤
      3 * (tree.leaves * blocks + tree.forks * guideSize) +
        3 * K * tree.projected.nodes + attempts * (tree.leaves * width) := by
  have hc := tree.structural_sum_caps blocks width guideSize h
  rw [bitBudget_sum, nodes_eq]
  nlinarith [hc.1, hc.2.1, hc.2.2]

theorem scheduledBitBudget_structural_bound (tree : ProposalTree) (blocks width guideSize : ℕ)
    (h : tree.StructuralCaps blocks width guideSize) (epsilon : ℚ) :
    tree.bitBudget (tree.precision epsilon) (tree.precision epsilon) ≤
      3 * (tree.leaves * blocks + tree.forks * guideSize) +
        tree.precision epsilon * (3 * tree.projected.nodes + tree.leaves * width) := by
  have hb := tree.bitBudget_structural_bound blocks width guideSize
    (tree.precision epsilon) (tree.precision epsilon) h
  convert hb using 1
  ring

theorem scheduled_precision_word_cap (tree : ProposalTree) (epsilon : ℚ) (he : 0 < epsilon) :
    tree.precision epsilon ≤ 6 + binaryWordWidth (16 * tree.nodeTolerance epsilon).den :=
  leafPrecision_denominator_width _ (tree.nodeTolerance_positive epsilon he)

theorem scheduled_seed_word_cap (tree : ProposalTree) (blocks width guideSize : ℕ)
    (h : tree.StructuralCaps blocks width guideSize) (epsilon : ℚ) (he : 0 < epsilon) :
    tree.bitBudget (tree.precision epsilon) (tree.precision epsilon) ≤
      3 * (tree.leaves * blocks + tree.forks * guideSize) +
        (6 + binaryWordWidth (16 * tree.nodeTolerance epsilon).den) *
          (3 * tree.projected.nodes + tree.leaves * width) := by
  have hb := tree.scheduledBitBudget_structural_bound blocks width guideSize h epsilon
  exact hb.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (tree.scheduled_precision_word_cap epsilon he)) _)

end Blotto.ImplicitLeafCounts.ProposalTree
