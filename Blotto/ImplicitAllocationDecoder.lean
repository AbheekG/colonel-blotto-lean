import Blotto.ImplicitScheduledOutput
import Blotto.ProductEpsilonSampler

/-! Actual implicit sampler labels decode to complete rational allocation rows.
The product-tree conversion is a semantic view, not an enumerated sampler;
native draws remain the compact callback/rejection runner. Local nonnegative
decoded bids derive every coordinate's nonnegativity. -/

namespace Blotto.ImplicitLeafCounts.ProposalTree
open scoped BigOperators Classical

def NonnegativeResources : ProposalTree → Prop
  | .leaf data _ _ => ∀ code : Fin (data.cap + 1), 0 ≤ data.decode code.val
  | .fork _ _ left right => left.NonnegativeResources ∧ right.NonnegativeResources

def allocationTree : (tree : ProposalTree) → tree.NonnegativeResources → ProductBidTree
  | .leaf data guide gamma, hn => .leaf data.family hn guide gamma
  | .fork guide gamma left right, hn => .fork guide gamma (left.allocationTree hn.1) (right.allocationTree hn.2)

theorem allocationTree_projected (tree : ProposalTree) (hn : tree.NonnegativeResources) :
    (tree.allocationTree hn).guideTree = tree.projected := by
  induction tree with
  | leaf data guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    simp only [allocationTree, ProductBidTree.guideTree, projected, ihL, ihR]

theorem allocationTree_labels (tree : ProposalTree) (hn : tree.NonnegativeResources) :
    (tree.allocationTree hn).labels = tree.projected.trueSize := by
  rw [← (tree.allocationTree hn).guideTree_trueSize, tree.allocationTree_projected hn]

def decodeLabel (tree : ProposalTree) (hn : tree.NonnegativeResources)
    (label : Fin tree.projected.trueSize) : Fin (tree.allocationTree hn).fields → ℚ :=
  (tree.allocationTree hn).decode (label.cast (tree.allocationTree_labels hn).symm)

noncomputable def targetAllocation (tree : ProposalTree) (hn : tree.NonnegativeResources)
    (label : Fin tree.projected.real.trueSize) : Allocation (tree.allocationTree hn).fields :=
  fun field => (tree.decodeLabel hn (label.cast tree.projected.real_trueSize) field : ℝ)

theorem decodeLabel_resource (tree : ProposalTree) (hn : tree.NonnegativeResources)
    (label : Fin tree.projected.trueSize) :
    (∑ field, (tree.decodeLabel hn label field : ℝ)) =
      tree.projected.real.trueFamily.resource (label.cast tree.projected.real_trueSize.symm) := by
  let view := tree.allocationTree hn
  let index := label.cast (tree.allocationTree_labels hn).symm
  have hs := view.realRow_sum index
  have hr := view.resource_eq_trueFamily index
  have hTransport : ∀ (first last : RationalWeightedGuideTree) (he : first = last)
      (i : Fin first.real.trueSize) (j : Fin last.real.trueSize), i.val = j.val →
      first.real.trueFamily.resource i = last.real.trueFamily.resource j := by
    intro first last he i j hv
    subst last
    have hij : i = j := Fin.ext hv
    rw [hij]
  have he := hTransport view.guideTree tree.projected (tree.allocationTree_projected hn)
    (index.cast (view.guideTree.real_trueSize.trans view.guideTree_trueSize).symm)
    (label.cast tree.projected.real_trueSize.symm) rfl
  exact hs.trans (hr.trans he)

def epsilonRow (tree : ProposalTree) (hn : tree.NonnegativeResources)
    (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ)
    (fallback : Fin tree.projected.trueSize) (bits : Fin (tree.epsilonSeedBudget epsilon) → Bool) :
    Fin (tree.allocationTree hn).fields → ℚ :=
  tree.decodeLabel hn (tree.epsilonOutput hc budget hm epsilon fallback bits)

theorem epsilonRow_feasible (tree : ProposalTree) (hn : tree.NonnegativeResources)
    (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ) (he : 0 < epsilon)
    (fallback : Fin tree.projected.trueSize)
    (hf : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ))
    (bits : Fin (tree.epsilonSeedBudget epsilon) → Bool) :
    Feasible (budget : ℝ) (fun field => (tree.epsilonRow hn hc budget hm epsilon fallback bits field : ℝ)) := by
  have hcOutput := (tree.epsilonOutput_contract hc budget hm epsilon he fallback hf).1 bits
  constructor
  · intro field
    change (0 : ℝ) ≤ ((tree.allocationTree hn).decode
      ((tree.epsilonOutput hc budget hm epsilon fallback bits).cast (tree.allocationTree_labels hn).symm) field : ℝ)
    exact_mod_cast (tree.allocationTree hn).decode_nonnegative
      ((tree.epsilonOutput hc budget hm epsilon fallback bits).cast (tree.allocationTree_labels hn).symm) field
  · rw [epsilonRow, tree.decodeLabel_resource hn]
    exact hcOutput

theorem epsilonRow_mean_error (tree : ProposalTree) (hn : tree.NonnegativeResources)
    (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ) (he : 0 < epsilon)
    (fallback : Fin tree.projected.trueSize)
    (hf : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ))
    (test : Allocation (tree.allocationTree hn).fields → ℝ) (ht : ∀ row, 0 ≤ test row ∧ test row ≤ 1) :
    |(fairBitKernel (tree.epsilonSeedBudget epsilon)).mean
      (fun bits => test (fun field => (tree.epsilonRow hn hc budget hm epsilon fallback bits field : ℝ))) -
      (tree.projected.targetKernel budget hm).mean (fun label => test (tree.targetAllocation hn label))| ≤ (epsilon : ℝ) := by
  have he := (tree.epsilonOutput_contract hc budget hm epsilon he fallback hf).2
    (fun label => test (tree.targetAllocation hn label)) (fun label => ht _)
  exact he

theorem epsilonRow_cdf_error (tree : ProposalTree) (hn : tree.NonnegativeResources)
    (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ) (he : 0 < epsilon)
    (fallback : Fin tree.projected.trueSize)
    (hf : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ))
    (field : Fin (tree.allocationTree hn).fields) (threshold : ℝ) :
    |(fairBitKernel (tree.epsilonSeedBudget epsilon)).mean
      (fun bits => if (tree.epsilonRow hn hc budget hm epsilon fallback bits field : ℝ) ≤ threshold then 1 else 0) -
      (tree.projected.targetKernel budget hm).mean
        (fun label => if tree.targetAllocation hn label field ≤ threshold then 1 else 0)| ≤ (epsilon : ℝ) :=
  tree.epsilonRow_mean_error hn hc budget hm epsilon he fallback hf
    (fun row => if row field ≤ threshold then 1 else 0) (fun row => by split_ifs <;> norm_num)

theorem epsilonRow_event_error (tree : ProposalTree) (hn : tree.NonnegativeResources)
    (hc : tree.projected.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.projected.real.trueFamily.prefixMass (budget : ℝ)) (epsilon : ℚ) (he : 0 < epsilon)
    (fallback : Fin tree.projected.trueSize)
    (hf : tree.projected.real.trueFamily.resource (fallback.cast tree.projected.real_trueSize.symm) ≤ (budget : ℝ))
    (event : Set (Allocation (tree.allocationTree hn).fields)) :
    |(fairBitKernel (tree.epsilonSeedBudget epsilon)).mean
      (fun bits => if (fun field => (tree.epsilonRow hn hc budget hm epsilon fallback bits field : ℝ)) ∈ event then 1 else 0) -
      (tree.projected.targetKernel budget hm).mean
        (fun label => if tree.targetAllocation hn label ∈ event then 1 else 0)| ≤ (epsilon : ℝ) :=
  tree.epsilonRow_mean_error hn hc budget hm epsilon he fallback hf
    (fun row => if row ∈ event then 1 else 0) (fun row => by split_ifs <;> norm_num)

end Blotto.ImplicitLeafCounts.ProposalTree
