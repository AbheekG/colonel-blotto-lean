import Blotto.ConstructedImplicitProposalTree
import Blotto.ImplicitAllocationDecoder

/-! Actual implicit guide rebuilding preserves nonnegative leaf resources and
every complete labelled allocation row. Only access guides change; the original
feasible game and duplicate Cartesian labels are retained exactly. -/

namespace Blotto
namespace ImplicitLeafCounts
namespace ProposalTree

theorem rebuild_nonnegativeResources (tree : ProposalTree) (hn : tree.NonnegativeResources)
    (gamma : ℚ) (hg : 1 ≤ gamma) : (tree.rebuildGuides gamma hg).NonnegativeResources := by
  induction tree with
  | leaf data guide g => exact hn
  | fork guide g left right ihL ihR => exact ⟨ihL hn.1, ihR hn.2⟩

theorem rebuild_allocation_fields (tree : ProposalTree) (hn : tree.NonnegativeResources)
    (gamma : ℚ) (hg : 1 ≤ gamma) :
    ((tree.rebuildGuides gamma hg).allocationTree (tree.rebuild_nonnegativeResources hn gamma hg)).fields =
      (tree.allocationTree hn).fields := by
  induction tree with
  | leaf data guide g => rfl
  | fork guide g left right ihL ihR =>
    change ((left.rebuildGuides gamma hg).allocationTree _).fields + ((right.rebuildGuides gamma hg).allocationTree _).fields = _
    rw [ihL hn.1, ihR hn.2]
    rfl

theorem rebuild_allocation_labels (tree : ProposalTree) (hn : tree.NonnegativeResources)
    (gamma : ℚ) (hg : 1 ≤ gamma) :
    ((tree.rebuildGuides gamma hg).allocationTree (tree.rebuild_nonnegativeResources hn gamma hg)).labels =
      (tree.allocationTree hn).labels := by
  rw [allocationTree_labels, tree.rebuild_trueSize, ← tree.allocationTree_labels hn]

theorem rebuild_allocation_decode (tree : ProposalTree) (hn : tree.NonnegativeResources)
    (gamma : ℚ) (hg : 1 ≤ gamma) (label : Fin (tree.allocationTree hn).labels)
    (field : Fin (tree.allocationTree hn).fields) :
    ((tree.rebuildGuides gamma hg).allocationTree (tree.rebuild_nonnegativeResources hn gamma hg)).decode
      (label.cast (tree.rebuild_allocation_labels hn gamma hg).symm)
      (field.cast (tree.rebuild_allocation_fields hn gamma hg).symm) = (tree.allocationTree hn).decode label field := by
  induction tree with
  | leaf data guide g => rfl
  | fork guide g left right ihL ihR =>
    let leftOld := left.allocationTree hn.1
    let rightOld := right.allocationTree hn.2
    let leftNew := (left.rebuildGuides gamma hg).allocationTree (left.rebuild_nonnegativeResources hn.1 gamma hg)
    let rightNew := (right.rebuildGuides gamma hg).allocationTree (right.rebuild_nonnegativeResources hn.2 gamma hg)
    let pair := finProdFinEquiv.symm label
    have hPair : finProdFinEquiv
        (pair.1.cast (left.rebuild_allocation_labels hn.1 gamma hg).symm,
          pair.2.cast (right.rebuild_allocation_labels hn.2 gamma hg).symm) =
        label.cast ((fork guide g left right).rebuild_allocation_labels hn gamma hg).symm := by
      apply Fin.ext
      have hLabel := congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv label)
      simp only [finProdFinEquiv_apply_val, Fin.val_cast] at hLabel ⊢
      rw [right.rebuild_allocation_labels hn.2 gamma hg]
      exact hLabel
    have hPair' : finProdFinEquiv.symm
        (label.cast ((fork guide g left right).rebuild_allocation_labels hn gamma hg).symm) =
        (pair.1.cast (left.rebuild_allocation_labels hn.1 gamma hg).symm,
          pair.2.cast (right.rebuild_allocation_labels hn.2 gamma hg).symm) := by
      exact (Equiv.symm_apply_apply finProdFinEquiv _).symm.trans
        (congrArg (fun index => finProdFinEquiv.symm index) hPair) |>.symm
    refine Fin.addCases ?_ ?_ field
    · intro j
      have hField : (Fin.castAdd rightOld.fields j).cast
          ((fork guide g left right).rebuild_allocation_fields hn gamma hg).symm =
          Fin.castAdd rightNew.fields (j.cast (left.rebuild_allocation_fields hn.1 gamma hg).symm) := Fin.ext rfl
      let value : Fin (leftNew.labels * rightNew.labels) → Fin (leftNew.fields + rightNew.fields) → ℚ :=
        fun index field => Fin.addCases (leftNew.decode (finProdFinEquiv.symm index).1)
          (rightNew.decode (finProdFinEquiv.symm index).2) field
      have hCoord := congrArg (fun field => value
        (label.cast ((fork guide g left right).rebuild_allocation_labels hn gamma hg).symm) field) hField
      have hRow := congrArg (fun labels : Fin leftNew.labels × Fin rightNew.labels =>
        Fin.addCases (motive := fun _ => ℚ) (leftNew.decode labels.1) (rightNew.decode labels.2)
          (Fin.castAdd rightNew.fields (j.cast (left.rebuild_allocation_fields hn.1 gamma hg).symm))) hPair'
      have he := hCoord.trans hRow
      rw [Fin.addCases_left] at he
      have hOld : ((fork guide g left right).allocationTree hn).decode label (Fin.castAdd rightOld.fields j) = leftOld.decode pair.1 j := by
        change Fin.addCases (motive := fun _ => ℚ) (leftOld.decode pair.1) (rightOld.decode pair.2) (Fin.castAdd rightOld.fields j) = _
        exact Fin.addCases_left j
      exact (he.trans (ihL hn.1 pair.1 j)).trans hOld.symm
    · intro j
      have hField : (Fin.natAdd leftOld.fields j).cast
          ((fork guide g left right).rebuild_allocation_fields hn gamma hg).symm =
          Fin.natAdd leftNew.fields (j.cast (right.rebuild_allocation_fields hn.2 gamma hg).symm) := by
        apply Fin.ext
        exact congrArg (fun count => count + j.val) (left.rebuild_allocation_fields hn.1 gamma hg).symm
      let value : Fin (leftNew.labels * rightNew.labels) → Fin (leftNew.fields + rightNew.fields) → ℚ :=
        fun index field => Fin.addCases (leftNew.decode (finProdFinEquiv.symm index).1)
          (rightNew.decode (finProdFinEquiv.symm index).2) field
      have hCoord := congrArg (fun field => value
        (label.cast ((fork guide g left right).rebuild_allocation_labels hn gamma hg).symm) field) hField
      have hRow := congrArg (fun labels : Fin leftNew.labels × Fin rightNew.labels =>
        Fin.addCases (motive := fun _ => ℚ) (leftNew.decode labels.1) (rightNew.decode labels.2)
          (Fin.natAdd leftNew.fields (j.cast (right.rebuild_allocation_fields hn.2 gamma hg).symm))) hPair'
      have he := hCoord.trans hRow
      rw [Fin.addCases_right] at he
      have hOld : ((fork guide g left right).allocationTree hn).decode label (Fin.natAdd leftOld.fields j) = rightOld.decode pair.2 j := by
        change Fin.addCases (motive := fun _ => ℚ) (leftOld.decode pair.1) (rightOld.decode pair.2) (Fin.natAdd leftOld.fields j) = _
        exact Fin.addCases_right j
      exact (he.trans (ihR hn.2 pair.2 j)).trans hOld.symm

end ProposalTree
end ImplicitLeafCounts
end Blotto
