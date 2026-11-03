import Blotto.RationalRejectionNativeContract

/-! Cartesian true labels decode to complete hard-budget allocation rows.
Every leaf is one battlefield with a nonnegative rational bid family. A fork
concatenates its two whole rows; no coordinates are independently resampled. -/

namespace Blotto
open scoped BigOperators

inductive ProductBidTree where
  | leaf {n p : ℕ} (family : RationalWeightedFamily n)
      (bid_nonnegative : ∀ i, 0 ≤ family.resource i)
      (guide : RationalWeightedFamily p) (gamma : ℚ)
  | fork {p : ℕ} (guide : RationalWeightedFamily p) (gamma : ℚ)
      (left right : ProductBidTree)

namespace ProductBidTree

def fields : ProductBidTree → ℕ
  | .leaf _ _ _ _ => 1
  | .fork _ _ left right => left.fields + right.fields

def labels : ProductBidTree → ℕ
  | .leaf (n := n) _ _ _ _ => n
  | .fork _ _ left right => left.labels * right.labels

def guideTree : ProductBidTree → RationalWeightedGuideTree
  | .leaf family _ guide gamma => .leaf family guide gamma
  | .fork guide gamma left right => .fork guide gamma left.guideTree right.guideTree

theorem guideTree_trueSize (tree : ProductBidTree) : tree.guideTree.trueSize = tree.labels := by
  induction tree with
  | leaf family hn guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    simp only [guideTree, RationalWeightedGuideTree.trueSize, labels, ihL, ihR]

def decode : (tree : ProductBidTree) → Fin tree.labels → Fin tree.fields → ℚ
  | .leaf family _ _ _, label => fun _ => family.resource label
  | .fork _ _ left right, label =>
      let pair := finProdFinEquiv.symm label
      Fin.addCases (left.decode pair.1) (right.decode pair.2)

def resource : (tree : ProductBidTree) → Fin tree.labels → ℚ
  | .leaf family _ _ _, label => family.resource label
  | .fork _ _ left right, label =>
      let pair := finProdFinEquiv.symm label
      left.resource pair.1 + right.resource pair.2

theorem fields_positive (tree : ProductBidTree) : 0 < tree.fields := by
  induction tree with
  | leaf family hn guide gamma => exact Nat.zero_lt_one
  | fork guide gamma left right ihL ihR =>
    change 0 < left.fields + right.fields
    omega

theorem decode_nonnegative (tree : ProductBidTree) (label : Fin tree.labels) :
    ∀ field, 0 ≤ tree.decode label field := by
  induction tree with
  | leaf family hn guide gamma => intro field; exact hn label
  | fork guide gamma left right ihL ihR =>
    intro field
    refine Fin.addCases ?_ ?_ field
    · intro i
      change (0 : ℚ) ≤ Fin.addCases (left.decode (finProdFinEquiv.symm label).1)
        (right.decode (finProdFinEquiv.symm label).2) (Fin.castAdd right.fields i)
      rw [Fin.addCases_left]
      exact ihL _ i
    · intro i
      change (0 : ℚ) ≤ Fin.addCases (left.decode (finProdFinEquiv.symm label).1)
        (right.decode (finProdFinEquiv.symm label).2) (Fin.natAdd left.fields i)
      rw [Fin.addCases_right]
      exact ihR _ i

theorem decode_sum (tree : ProductBidTree) (label : Fin tree.labels) :
    (∑ field, tree.decode label field) = tree.resource label := by
  induction tree with
  | leaf family hn guide gamma =>
    change (∑ _ : Fin 1, family.resource label) = family.resource label
    simp
  | fork guide gamma left right ihL ihR =>
    change (∑ field : Fin (left.fields + right.fields),
      Fin.addCases (left.decode (finProdFinEquiv.symm label).1)
        (right.decode (finProdFinEquiv.symm label).2) field) =
      left.resource (finProdFinEquiv.symm label).1 + right.resource (finProdFinEquiv.symm label).2
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, ihL, ihR]

noncomputable def realRow (tree : ProductBidTree) (label : Fin tree.labels) : Allocation tree.fields :=
  fun field => (tree.decode label field : ℝ)

theorem realRow_sum (tree : ProductBidTree) (label : Fin tree.labels) :
    (∑ field, tree.realRow label field) = (tree.resource label : ℝ) := by
  unfold realRow
  rw [← Rat.cast_sum, decode_sum]

theorem realRow_feasible (tree : ProductBidTree) (label : Fin tree.labels) (budget : ℚ)
    (h : tree.resource label ≤ budget) : Feasible (budget : ℝ) (tree.realRow label) := by
  constructor
  · intro field
    change (0 : ℝ) ≤ (tree.decode label field : ℝ)
    exact_mod_cast tree.decode_nonnegative label field
  · rw [realRow_sum]
    exact_mod_cast h

theorem resource_eq_trueFamily (tree : ProductBidTree) (label : Fin tree.labels) :
    (tree.resource label : ℝ) = tree.guideTree.real.trueFamily.resource
      (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm) := by
  induction tree with
  | leaf family hn guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    let pair := finProdFinEquiv.symm label
    have hleft := ihL pair.1
    have hright := ihR pair.2
    change ((left.resource pair.1 + right.resource pair.2 : ℚ) : ℝ) =
      (left.guideTree.real.trueFamily.product right.guideTree.real.trueFamily).resource
        (label.cast ((fork guide gamma left right).guideTree.real_trueSize.trans
          (fork guide gamma left right).guideTree_trueSize).symm)
    rw [Rat.cast_add, hleft, hright]
    have hlabel : label.cast ((fork guide gamma left right).guideTree.real_trueSize.trans
          (fork guide gamma left right).guideTree_trueSize).symm =
        finProdFinEquiv
          (pair.1.cast (left.guideTree.real_trueSize.trans left.guideTree_trueSize).symm,
            pair.2.cast (right.guideTree.real_trueSize.trans right.guideTree_trueSize).symm) := by
      apply Fin.ext
      have hp := congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv label)
      change label.val = _
      simp only [finProdFinEquiv_apply_val, Fin.val_cast]
      simp only [finProdFinEquiv_apply_val] at hp
      have hs : right.guideTree.real.trueSize = right.labels :=
        right.guideTree.real_trueSize.trans right.guideTree_trueSize
      rw [hs]
      exact hp.symm
    have hr := congrArg (fun k : Fin (left.guideTree.real.trueSize * right.guideTree.real.trueSize) =>
      (left.guideTree.real.trueFamily.product right.guideTree.real.trueFamily).resource k) hlabel
    rw [WeightedResourceFamily.product_resource] at hr
    exact hr.symm

def rejectionRow (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified) (budget : ℚ)
    (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (K attempts : ℕ)
    (fallback : Fin tree.labels)
    (bits : Fin (attempts * tree.guideTree.attemptBitBudget K) → Bool) : Fin tree.fields → ℚ :=
  tree.decode ((tree.guideTree.rejectionNativeOutput hc budget hm K attempts
    (fallback.cast tree.guideTree_trueSize.symm) bits).cast tree.guideTree_trueSize)

theorem rejectionRow_feasible (tree : ProductBidTree) (hc : tree.guideTree.real.LowerCertified)
    (budget : ℚ) (hm : 0 < tree.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (K attempts : ℕ)
    (fallback : Fin tree.labels) (hf : tree.resource fallback ≤ budget)
    (bits : Fin (attempts * tree.guideTree.attemptBitBudget K) → Bool) :
    Feasible (budget : ℝ) (fun field => (tree.rejectionRow hc budget hm K attempts fallback bits field : ℝ)) := by
  have hfReal : tree.guideTree.real.trueFamily.resource
      ((fallback.cast tree.guideTree_trueSize.symm).cast tree.guideTree.real_trueSize.symm) ≤ (budget : ℝ) := by
    have he := tree.resource_eq_trueFamily fallback
    have hi : (fallback.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm) =
      ((fallback.cast tree.guideTree_trueSize.symm).cast tree.guideTree.real_trueSize.symm) := Fin.ext rfl
    rw [hi] at he
    rw [← he]
    exact_mod_cast hf
  have hout := tree.guideTree.rejectionNativeOutput_feasible hc budget hm K attempts
    (fallback.cast tree.guideTree_trueSize.symm) hfReal bits
  let label := (tree.guideTree.rejectionNativeOutput hc budget hm K attempts
    (fallback.cast tree.guideTree_trueSize.symm) bits).cast tree.guideTree_trueSize
  have he := tree.resource_eq_trueFamily label
  have hi : label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm =
    (tree.guideTree.rejectionNativeOutput hc budget hm K attempts
      (fallback.cast tree.guideTree_trueSize.symm) bits).cast tree.guideTree.real_trueSize.symm := Fin.ext rfl
  rw [hi] at he
  have hresource : tree.resource label ≤ budget := by
    have hr : (tree.resource label : ℝ) ≤ (budget : ℝ) := by rw [he]; exact hout
    exact_mod_cast hr
  exact tree.realRow_feasible label budget hresource

end ProductBidTree
end Blotto
