import Blotto.ImplicitLeafDirectAccess
import Blotto.ImplicitCertifiedGuide
import Blotto.ConstructedImplicitProposalTree

/-! Native upper/lower leaf preparation uses stored exact access callbacks.
It computes the same full-plateau bins as the retained constructor, while
the concrete Farey callback avoids monotone decoder binary search. -/

namespace Blotto.ImplicitLeafCounts.LeafAccess
open ImplicitLeafCounts

def plateauEnd {leaf : ProposalLeaf} (access : LeafAccess leaf) (start : ℕ) : ℕ :=
  min leaf.cap (access.strict (leaf.decode start) - 1)

def binEnd {leaf : ProposalLeaf} (access : LeafAccess leaf) (gamma : ℚ) (start : ℕ) : ℕ :=
  let target := gamma * prefixMass leaf.blocks (access.plateauEnd start : ℤ)
  if totalMass leaf.blocks ≤ target then leaf.cap else
    match inverseStrict leaf.blocks target with
    | none => leaf.cap
    | some crossing => access.weak (leaf.decode crossing) - 1

def binStep {leaf : ProposalLeaf} (access : LeafAccess leaf) (gamma : ℚ) (start : ℕ) : UpperBin :=
  let last := access.binEnd gamma start
  ⟨leaf.decode start, start, last, prefixMass leaf.blocks (last : ℤ) - prefixMass leaf.blocks ((start : ℤ) - 1)⟩

def bins {leaf : ProposalLeaf} (access : LeafAccess leaf) (gamma : ℚ) (start : ℕ) : List UpperBin :=
  if start ≤ leaf.cap then
    let bin := access.binStep gamma start
    if start ≤ bin.hi then bin :: access.bins gamma (bin.hi + 1) else []
  else []
termination_by leaf.cap + 1 - start
decreasing_by
  simp_wf
  have _hs : start ≤ leaf.cap := by assumption
  have hp : start ≤ (access.binStep gamma start).hi := by assumption
  omega

def upperAtoms {leaf : ProposalLeaf} (access : LeafAccess leaf) (gamma : ℚ) : List CumulativeGuidePruning.Atom :=
  (access.bins gamma 0).map (fun bin => (bin.resource, bin.mass))

def lowerAtoms {leaf : ProposalLeaf} (access : LeafAccess leaf) (gamma : ℚ) : List CumulativeGuidePruning.Atom :=
  (access.upperAtoms gamma).map (fun atom => (atom.1, atom.2 / gamma))

theorem plateauEnd_eq {leaf : ProposalLeaf} (access : LeafAccess leaf) (start : ℕ) :
    access.plateauEnd start = ImplicitLeafCounts.plateauEnd leaf.cap leaf.decode start := by
  unfold plateauEnd ImplicitLeafCounts.plateauEnd
  rw [access.strict_eq]

theorem binEnd_eq {leaf : ProposalLeaf} (access : LeafAccess leaf) (gamma : ℚ) (start : ℕ) :
    access.binEnd gamma start = upperBinEnd leaf.cap leaf.blocks leaf.decode gamma start := by
  unfold binEnd upperBinEnd
  rw [access.plateauEnd_eq]
  simp_rw [access.weak_eq]
  rfl

theorem binStep_eq {leaf : ProposalLeaf} (access : LeafAccess leaf) (gamma : ℚ) (start : ℕ) :
    access.binStep gamma start = upperBinStep leaf.cap leaf.blocks leaf.decode gamma start := by
  unfold binStep upperBinStep
  rw [access.binEnd_eq]

theorem bins_eq {leaf : ProposalLeaf} (access : LeafAccess leaf) (gamma : ℚ) (start : ℕ) :
    access.bins gamma start = upperBins leaf.cap leaf.blocks leaf.decode gamma start := by
  fun_induction bins
  all_goals rw [upperBins]
  all_goals simp_all (config := { zetaDelta := true }) only [access.binStep_eq, ite_true, ite_false]

theorem upperAtoms_eq {leaf : ProposalLeaf} (access : LeafAccess leaf) (gamma : ℚ) :
    access.upperAtoms gamma = upperGuide leaf.cap leaf.blocks leaf.decode gamma := by
  unfold upperAtoms upperGuide
  rw [access.bins_eq]

theorem lowerAtoms_eq {leaf : ProposalLeaf} (access : LeafAccess leaf) (gamma : ℚ) :
    access.lowerAtoms gamma = leaf.lowerGuideAtoms gamma := by
  unfold lowerAtoms ProposalLeaf.lowerGuideAtoms
  rw [access.upperAtoms_eq]

theorem lowerAtoms_nonnegative {leaf : ProposalLeaf} (access : LeafAccess leaf) (gamma : ℚ) (hg : 1 ≤ gamma) :
    CumulativeGuidePruning.Nonnegative (access.lowerAtoms gamma) := by
  rw [access.lowerAtoms_eq]
  exact leaf.lowerGuideAtoms_nonnegative gamma hg

def lowerNode {leaf : ProposalLeaf} (access : LeafAccess leaf) (gamma : ℚ) (hg : 1 ≤ gamma) : ProposalTree :=
  .leaf leaf (CumulativeGuidePruning.rationalFamily (access.lowerAtoms gamma) (access.lowerAtoms_nonnegative gamma hg)) gamma

theorem atom_leaf_congr (leaf : ProposalLeaf) (gamma : ℚ) (first second : List CumulativeGuidePruning.Atom)
    (hf : CumulativeGuidePruning.Nonnegative first) (hs : CumulativeGuidePruning.Nonnegative second) (h : first = second) :
    (ProposalTree.leaf leaf (CumulativeGuidePruning.rationalFamily first hf) gamma) =
      ProposalTree.leaf leaf (CumulativeGuidePruning.rationalFamily second hs) gamma := by
  cases h
  rfl

theorem lowerNode_eq {leaf : ProposalLeaf} (access : LeafAccess leaf) (gamma : ℚ) (hg : 1 ≤ gamma) :
    access.lowerNode gamma hg = ProposalTree.leaf leaf (leaf.lowerGuide gamma hg) gamma :=
  atom_leaf_congr leaf gamma _ _ _ _ (access.lowerAtoms_eq gamma)

end Blotto.ImplicitLeafCounts.LeafAccess
