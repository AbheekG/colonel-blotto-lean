import Blotto.ImplicitUpperGuideDirectAccess
import Blotto.ImplicitProposalDirectAccess

/-! Prepared trees rebuild their actual leaf guides through stored direct
callbacks. Internal exact guide-pair construction is unchanged and charged
separately. The produced tree is proved identical to the retained construction;
native access is stored with it for subsequent proposals and importance. -/

namespace Blotto.ImplicitLeafCounts

structure AccessedTree where
  model : ProposalTree
  access : TreeAccess model

def mergeAccessModels (left right : ProposalTree) (gamma : ℚ) : ProposalTree :=
  .fork (CumulativeInternalGuide.internalGuide left.projected.guide right.projected.guide gamma) gamma left right

def rebuildAccess : (tree : ProposalTree) → TreeAccess tree → (gamma : ℚ) → (hg : 1 ≤ gamma) → AccessedTree
  | .leaf _data _ _, access, gamma, hg =>
    { model := access.lowerNode gamma hg
      access := access }
  | .fork _ _ left right, access, gamma, hg =>
    let leftNew := rebuildAccess left access.1 gamma hg
    let rightNew := rebuildAccess right access.2 gamma hg
    { model := mergeAccessModels leftNew.model rightNew.model gamma
      access := (leftNew.access, rightNew.access) }

theorem rebuildAccess_model_eq (tree : ProposalTree) (access : TreeAccess tree) (gamma : ℚ) (hg : 1 ≤ gamma) :
    (rebuildAccess tree access gamma hg).model = tree.rebuildGuides gamma hg := by
  induction tree with
  | leaf data guide g => exact access.lowerNode_eq gamma hg
  | fork guide g left right ihL ihR =>
    change mergeAccessModels (rebuildAccess left access.1 gamma hg).model (rebuildAccess right access.2 gamma hg).model gamma =
      mergeAccessModels (left.rebuildGuides gamma hg) (right.rebuildGuides gamma hg) gamma
    exact congrArg₂ (fun l r => mergeAccessModels l r gamma) (ihL access.1) (ihR access.2)

def constructAccess (tree : ProposalTree) (access : TreeAccess tree) : AccessedTree :=
  rebuildAccess tree access tree.constructionGamma tree.constructionGamma_ge_one

theorem constructAccess_model_eq (tree : ProposalTree) (access : TreeAccess tree) :
    (constructAccess tree access).model = tree.constructed :=
  rebuildAccess_model_eq tree access tree.constructionGamma tree.constructionGamma_ge_one

end Blotto.ImplicitLeafCounts
