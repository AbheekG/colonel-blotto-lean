import Blotto.ConstructedGuidePreservation
import Blotto.AdaptiveComputedRegret

/-! One selected field reweights the existing Cartesian labels by one local
multiplier. Bids/resources and hard feasibility are preserved; guide metadata
must be rebuilt separately. No expanded Cartesian table is stored by the update. -/

namespace Blotto
open scoped BigOperators
namespace ProductBidTree

/-- A label's actual local code at each field, including duplicate bids. -/
def code : (tree : ProductBidTree) → Fin tree.labels → Fin tree.fields → ℕ
  | .leaf _ _ _ _, label => fun _ => label.val
  | .fork _ _ left right, label =>
      let pair := finProdFinEquiv.symm label
      Fin.addCases (left.code pair.1) (right.code pair.2)

def weight : (tree : ProductBidTree) → Fin tree.labels → ℚ
  | .leaf family _ _ _, label => family.mass label
  | .fork _ _ left right, label =>
      let pair := finProdFinEquiv.symm label
      left.weight pair.1 * right.weight pair.2

theorem weight_nonnegative (tree : ProductBidTree) (label : Fin tree.labels) : 0 ≤ tree.weight label := by
  induction tree with
  | leaf family _ _ _ => exact family.mass_nonnegative label
  | fork _ _ left right ihL ihR => exact mul_nonneg (ihL _) (ihR _)

def reweight (tree : ProductBidTree) (multipliers : Fin tree.fields → ℕ → ℚ)
    (hn : ∀ field code, 0 ≤ multipliers field code) : ProductBidTree :=
  match tree with
  | .leaf family hBid guide gamma =>
      .leaf ⟨family.resource, fun label => family.mass label * multipliers (show Fin 1 from 0) label.val,
        fun label => mul_nonneg (family.mass_nonnegative label) (hn (show Fin 1 from 0) label.val)⟩ hBid guide gamma
  | .fork guide gamma left right =>
      .fork guide gamma
        (left.reweight (fun field => multipliers (Fin.castAdd right.fields field))
          (fun _field code => hn _ code))
        (right.reweight (fun field => multipliers (Fin.natAdd left.fields field))
          (fun _field code => hn _ code))

theorem reweight_fields (tree : ProductBidTree) (multipliers : Fin tree.fields → ℕ → ℚ)
    (hn : ∀ field code, 0 ≤ multipliers field code) : (tree.reweight multipliers hn).fields = tree.fields := by
  induction tree with
  | leaf family hBid guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    simp only [reweight, fields, ihL, ihR]

theorem reweight_labels (tree : ProductBidTree) (multipliers : Fin tree.fields → ℕ → ℚ)
    (hn : ∀ field code, 0 ≤ multipliers field code) : (tree.reweight multipliers hn).labels = tree.labels := by
  induction tree with
  | leaf family hBid guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    simp only [reweight, labels, ihL, ihR]

def reweightedLabel (tree : ProductBidTree) (multipliers : Fin tree.fields → ℕ → ℚ)
    (hn : ∀ field code, 0 ≤ multipliers field code) : Fin tree.labels → Fin (tree.reweight multipliers hn).labels
  | label => label.cast (tree.reweight_labels multipliers hn).symm

theorem reweight_resource (tree : ProductBidTree) (multipliers : Fin tree.fields → ℕ → ℚ)
    (hn : ∀ field code, 0 ≤ multipliers field code) (label : Fin tree.labels) :
    (tree.reweight multipliers hn).resource (tree.reweightedLabel multipliers hn label) = tree.resource label := by
  induction tree with
  | leaf family hBid guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    let ml := fun field => multipliers (Fin.castAdd right.fields field)
    let mr := fun field => multipliers (Fin.natAdd left.fields field)
    let hl := fun field code => hn (Fin.castAdd right.fields field) code
    let hr := fun field code => hn (Fin.natAdd left.fields field) code
    let pair := finProdFinEquiv.symm label
    have hp : (fork guide gamma left right).reweightedLabel multipliers hn label =
        finProdFinEquiv (left.reweightedLabel ml hl pair.1, right.reweightedLabel mr hr pair.2) := by
      apply Fin.ext
      have he := congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv label)
      simp only [finProdFinEquiv_apply_val, Fin.val_cast, reweightedLabel] at he ⊢
      rw [right.reweight_labels mr hr]
      exact he.symm
    change (left.reweight ml hl).resource (finProdFinEquiv.symm _).1 +
      (right.reweight mr hr).resource (finProdFinEquiv.symm _).2 =
      left.resource pair.1 + right.resource pair.2
    rw [hp, Equiv.symm_apply_apply, ihL ml hl pair.1, ihR mr hr pair.2]

def multiplierProduct : (tree : ProductBidTree) → (Fin tree.fields → ℕ → ℚ) → Fin tree.labels → ℚ
  | .leaf _ _ _ _, multipliers, label => multipliers (show Fin 1 from 0) label.val
  | .fork _ _ left right, multipliers, label =>
      let pair := finProdFinEquiv.symm label
      left.multiplierProduct (fun field => multipliers (Fin.castAdd right.fields field)) pair.1 *
        right.multiplierProduct (fun field => multipliers (Fin.natAdd left.fields field)) pair.2

theorem reweight_weight (tree : ProductBidTree) (multipliers : Fin tree.fields → ℕ → ℚ)
    (hn : ∀ field code, 0 ≤ multipliers field code) (label : Fin tree.labels) :
    (tree.reweight multipliers hn).weight (tree.reweightedLabel multipliers hn label) =
      tree.weight label * tree.multiplierProduct multipliers label := by
  induction tree with
  | leaf family hBid guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    let ml := fun field => multipliers (Fin.castAdd right.fields field)
    let mr := fun field => multipliers (Fin.natAdd left.fields field)
    let hl := fun field code => hn (Fin.castAdd right.fields field) code
    let hr := fun field code => hn (Fin.natAdd left.fields field) code
    let pair := finProdFinEquiv.symm label
    have hp : (fork guide gamma left right).reweightedLabel multipliers hn label =
        finProdFinEquiv (left.reweightedLabel ml hl pair.1, right.reweightedLabel mr hr pair.2) := by
      apply Fin.ext
      have he := congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv label)
      simp only [finProdFinEquiv_apply_val, Fin.val_cast, reweightedLabel] at he ⊢
      rw [right.reweight_labels mr hr]
      exact he.symm
    change (left.reweight ml hl).weight (finProdFinEquiv.symm _).1 *
      (right.reweight mr hr).weight (finProdFinEquiv.symm _).2 =
      (left.weight pair.1 * right.weight pair.2) *
        (left.multiplierProduct ml pair.1 * right.multiplierProduct mr pair.2)
    rw [hp, Equiv.symm_apply_apply, ihL ml hl pair.1, ihR mr hr pair.2]
    ring

theorem weight_eq_trueFamily (tree : ProductBidTree) (label : Fin tree.labels) :
    (tree.weight label : ℝ) = tree.guideTree.real.trueFamily.mass
      (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm) := by
  induction tree with
  | leaf family hBid guide gamma => rfl
  | fork guide gamma left right ihL ihR =>
    let pair := finProdFinEquiv.symm label
    have hp : label.cast ((fork guide gamma left right).guideTree.real_trueSize.trans
        (fork guide gamma left right).guideTree_trueSize).symm =
        finProdFinEquiv
          (pair.1.cast (left.guideTree.real_trueSize.trans left.guideTree_trueSize).symm,
            pair.2.cast (right.guideTree.real_trueSize.trans right.guideTree_trueSize).symm) := by
      apply Fin.ext
      have he := congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv label)
      simp only [finProdFinEquiv_apply_val, Fin.val_cast] at he ⊢
      rw [right.guideTree.real_trueSize.trans right.guideTree_trueSize]
      exact he.symm
    change ((left.weight pair.1 * right.weight pair.2 : ℚ) : ℝ) =
      (left.guideTree.real.trueFamily.product right.guideTree.real.trueFamily).mass _
    rw [hp, WeightedResourceFamily.product_mass, Rat.cast_mul, ihL, ihR]

theorem multiplierProduct_eq (tree : ProductBidTree) (multipliers : Fin tree.fields → ℕ → ℚ)
    (label : Fin tree.labels) : tree.multiplierProduct multipliers label =
      ∏ field, multipliers field (tree.code label field) := by
  induction tree with
  | leaf family hBid guide gamma =>
    change multipliers (show Fin 1 from 0) label.val = ∏ field : Fin 1, multipliers field label.val
    simp
  | fork guide gamma left right ihL ihR =>
    change left.multiplierProduct (fun field => multipliers (Fin.castAdd right.fields field)) _ *
      right.multiplierProduct (fun field => multipliers (Fin.natAdd left.fields field)) _ =
      ∏ field : Fin (left.fields + right.fields), multipliers field
        (Fin.addCases (left.code (finProdFinEquiv.symm label).1)
          (right.code (finProdFinEquiv.symm label).2) field)
    rw [Fin.prod_univ_add, ihL, ihR]
    simp only [Fin.addCases_left, Fin.addCases_right]

theorem multiplierProduct_selected (tree : ProductBidTree) (selected : Fin tree.fields)
    (multiplier : ℕ → ℚ) (label : Fin tree.labels) :
    tree.multiplierProduct (fun field code => if field = selected then multiplier code else 1) label =
      multiplier (tree.code label selected) := by
  rw [multiplierProduct_eq]
  simp

end ProductBidTree
end Blotto
