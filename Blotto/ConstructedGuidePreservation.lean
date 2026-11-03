import Blotto.ConstructedGuideFactor

/-! Rebuilding guides preserves every true label's complete row and resource. These equalities prevent replacing the original feasible game
by guide atoms: only proposal-access metadata is changed. -/

namespace Blotto
namespace ProductBidTree

theorem rebuild_resource (tree : ProductBidTree) (gamma : ℚ) (label : Fin tree.labels) :
    (tree.rebuildGuides gamma).resource (label.cast (tree.rebuild_labels gamma).symm) = tree.resource label := by
  induction tree with
  | leaf family hn guide g => rfl
  | fork guide g left right ihL ihR =>
    let pair := finProdFinEquiv.symm label
    have hp : finProdFinEquiv
        (pair.1.cast (left.rebuild_labels gamma).symm, pair.2.cast (right.rebuild_labels gamma).symm) =
        label.cast ((fork guide g left right).rebuild_labels gamma).symm := by
      apply Fin.ext
      have hlabel := congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv label)
      simp only [finProdFinEquiv_apply_val, Fin.val_cast] at hlabel ⊢
      have he := right.rebuild_labels gamma
      rw [he]
      exact hlabel
    have hLeft := ihL pair.1
    have hRight := ihR pair.2
    change (left.rebuildGuides gamma).resource (finProdFinEquiv.symm (label.cast ((fork guide g left right).rebuild_labels gamma).symm)).1 +
      (right.rebuildGuides gamma).resource (finProdFinEquiv.symm (label.cast ((fork guide g left right).rebuild_labels gamma).symm)).2 =
        left.resource pair.1 + right.resource pair.2
    have hpair := congrArg (fun k : Fin ((left.rebuildGuides gamma).labels * (right.rebuildGuides gamma).labels) =>
      finProdFinEquiv.symm k) hp
    have hpair' : finProdFinEquiv.symm (label.cast ((fork guide g left right).rebuild_labels gamma).symm) =
        (pair.1.cast (left.rebuild_labels gamma).symm, pair.2.cast (right.rebuild_labels gamma).symm) := by
      exact (Equiv.symm_apply_apply finProdFinEquiv _).symm.trans hpair |>.symm
    have hsum := congrArg (fun pr => (left.rebuildGuides gamma).resource pr.1 +
      (right.rebuildGuides gamma).resource pr.2) hpair'
    exact hsum.trans (congrArg₂ (· + ·) hLeft hRight)

theorem rebuild_decode (tree : ProductBidTree) (gamma : ℚ) (label : Fin tree.labels) (field : Fin tree.fields) :
    (tree.rebuildGuides gamma).decode (label.cast (tree.rebuild_labels gamma).symm)
      (field.cast (tree.rebuild_fields gamma).symm) = tree.decode label field := by
  induction tree with
  | leaf family hn guide g => rfl
  | fork guide g left right ihL ihR =>
    let pair := finProdFinEquiv.symm label
    have hp : finProdFinEquiv
        (pair.1.cast (left.rebuild_labels gamma).symm, pair.2.cast (right.rebuild_labels gamma).symm) =
        label.cast ((fork guide g left right).rebuild_labels gamma).symm := by
      apply Fin.ext
      have hlabel := congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv label)
      simp only [finProdFinEquiv_apply_val, Fin.val_cast] at hlabel ⊢
      rw [right.rebuild_labels gamma]
      exact hlabel
    have hpair := congrArg (fun k : Fin ((left.rebuildGuides gamma).labels * (right.rebuildGuides gamma).labels) =>
      finProdFinEquiv.symm k) hp
    have hpair' : finProdFinEquiv.symm (label.cast ((fork guide g left right).rebuild_labels gamma).symm) =
        (pair.1.cast (left.rebuild_labels gamma).symm, pair.2.cast (right.rebuild_labels gamma).symm) := by
      exact (Equiv.symm_apply_apply finProdFinEquiv _).symm.trans hpair |>.symm
    refine Fin.addCases ?_ ?_ field
    · intro i
      have hField : (Fin.castAdd right.fields i).cast ((fork guide g left right).rebuild_fields gamma).symm =
          Fin.castAdd (right.rebuildGuides gamma).fields (i.cast (left.rebuild_fields gamma).symm) := Fin.ext rfl
      let value : Fin ((left.rebuildGuides gamma).labels * (right.rebuildGuides gamma).labels) →
          Fin ((left.rebuildGuides gamma).fields + (right.rebuildGuides gamma).fields) → ℚ :=
        fun k j => Fin.addCases ((left.rebuildGuides gamma).decode (finProdFinEquiv.symm k).1)
          ((right.rebuildGuides gamma).decode (finProdFinEquiv.symm k).2) j
      have hcoord := congrArg (fun j => value
        (label.cast ((fork guide g left right).rebuild_labels gamma).symm) j) hField
      have hrow := congrArg (fun pr : Fin (left.rebuildGuides gamma).labels × Fin (right.rebuildGuides gamma).labels =>
        Fin.addCases (motive := fun _ => ℚ) ((left.rebuildGuides gamma).decode pr.1)
          ((right.rebuildGuides gamma).decode pr.2)
          (Fin.castAdd (right.rebuildGuides gamma).fields (i.cast (left.rebuild_fields gamma).symm))) hpair'
      have he := hcoord.trans hrow
      rw [Fin.addCases_left] at he
      have ht := ihL pair.1 i
      have hr : (fork guide g left right).decode label (Fin.castAdd right.fields i) = left.decode pair.1 i := by
        change Fin.addCases (motive := fun _ => ℚ) (left.decode pair.1) (right.decode pair.2) (Fin.castAdd right.fields i) = _
        exact Fin.addCases_left i
      exact (he.trans ht).trans hr.symm
    · intro i
      have hField : (Fin.natAdd left.fields i).cast ((fork guide g left right).rebuild_fields gamma).symm =
          Fin.natAdd (left.rebuildGuides gamma).fields (i.cast (right.rebuild_fields gamma).symm) := by
        apply Fin.ext
        exact congrArg (fun size => size + i.val) (left.rebuild_fields gamma).symm
      let value : Fin ((left.rebuildGuides gamma).labels * (right.rebuildGuides gamma).labels) →
          Fin ((left.rebuildGuides gamma).fields + (right.rebuildGuides gamma).fields) → ℚ :=
        fun k j => Fin.addCases ((left.rebuildGuides gamma).decode (finProdFinEquiv.symm k).1)
          ((right.rebuildGuides gamma).decode (finProdFinEquiv.symm k).2) j
      have hcoord := congrArg (fun j => value
        (label.cast ((fork guide g left right).rebuild_labels gamma).symm) j) hField
      have hrow := congrArg (fun pr : Fin (left.rebuildGuides gamma).labels × Fin (right.rebuildGuides gamma).labels =>
        Fin.addCases (motive := fun _ => ℚ) ((left.rebuildGuides gamma).decode pr.1)
          ((right.rebuildGuides gamma).decode pr.2)
          (Fin.natAdd (left.rebuildGuides gamma).fields (i.cast (right.rebuild_fields gamma).symm))) hpair'
      have he := hcoord.trans hrow
      rw [Fin.addCases_right] at he
      have ht := ihR pair.2 i
      have hr : (fork guide g left right).decode label (Fin.natAdd left.fields i) = right.decode pair.2 i := by
        change Fin.addCases (motive := fun _ => ℚ) (left.decode pair.1) (right.decode pair.2) (Fin.natAdd left.fields i) = _
        exact Fin.addCases_right i
      exact (he.trans ht).trans hr.symm

end ProductBidTree
end Blotto
