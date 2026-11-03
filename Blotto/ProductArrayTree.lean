import Blotto.ProductGibbsTraining
import Blotto.ConstructedGuideSchedule

/-! An actual nonempty right-comb tree is constructed from dependent finite
field arrays. Labels encode all original local codes, retaining duplicate bids.
Dummy guide metadata is replaced by the existing certified guide construction;
no label equivalence or guide certificate is assumed from the caller. -/

namespace Blotto
open scoped BigOperators
namespace ProductArrayTree

def dummyGuide : RationalWeightedFamily 0 where
  resource := Fin.elim0
  mass := Fin.elim0
  mass_nonnegative := fun i => Fin.elim0 i

def fieldFamily {m : ℕ} {sizes : Fin m → ℕ}
    (bids weights : (j : Fin m) → Fin (sizes j) → ℚ)
    (hw : ∀ j code, 0 ≤ weights j code) (j : Fin m) : RationalWeightedFamily (sizes j) where
  resource := bids j
  mass := weights j
  mass_nonnegative := hw j

def raw : (n : ℕ) → (sizes : Fin (n + 1) → ℕ) →
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ) →
    (∀ j code, 0 ≤ bids j code) → (∀ j code, 0 ≤ weights j code) → ProductBidTree
  | 0, _sizes, bids, weights, hb, hw =>
      .leaf (fieldFamily bids weights hw 0) (hb 0) dummyGuide 1
  | n + 1, sizes, bids, weights, hb, hw =>
      .fork dummyGuide 1
        (.leaf (fieldFamily bids weights hw 0) (hb 0) dummyGuide 1)
        (raw n (fun j => sizes j.succ) (fun j => bids j.succ) (fun j => weights j.succ)
          (fun j => hb j.succ) (fun j => hw j.succ))

theorem raw_fields (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 ≤ weights j code) :
    (raw n sizes bids weights hb hw).fields = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change 1 + (raw n _ _ _ _ _).fields = (n + 1) + 1
      rw [ih]
      omega

def headTailEquiv {n : ℕ} (sizes : Fin (n + 1) → ℕ) :
    SparseMW.ProductCodes sizes ≃ (Fin (sizes 0) × SparseMW.ProductCodes (fun j : Fin n => sizes j.succ)) where
  toFun := fun code => (code 0, fun j => code j.succ)
  invFun := fun pair => Fin.cons pair.1 pair.2
  left_inv := by intro code; funext j; refine Fin.cases ?_ ?_ j <;> simp
  right_inv := by intro pair; apply Prod.ext <;> simp

def oneFieldEquiv (sizes : Fin 1 → ℕ) : SparseMW.ProductCodes sizes ≃ Fin (sizes 0) where
  toFun := fun code => code 0
  invFun := fun code => Fin.cases code (fun i => Fin.elim0 i)
  left_inv := by intro code; funext j; fin_cases j; rfl
  right_inv := fun _ => rfl

def labelEquiv : (n : ℕ) → (sizes : Fin (n + 1) → ℕ) →
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ) →
    (hb : ∀ j code, 0 ≤ bids j code) → (hw : ∀ j code, 0 ≤ weights j code) →
    Fin (raw n sizes bids weights hb hw).labels ≃ SparseMW.ProductCodes sizes
  | 0, sizes, _bids, _weights, _hb, _hw => (oneFieldEquiv sizes).symm
  | n + 1, sizes, bids, weights, hb, hw =>
      finProdFinEquiv.symm |>.trans
        ((Equiv.prodCongr (Equiv.refl _) (labelEquiv n (fun j => sizes j.succ)
          (fun j => bids j.succ) (fun j => weights j.succ) (fun j => hb j.succ) (fun j => hw j.succ))).trans
            (headTailEquiv sizes).symm)

theorem raw_weight (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 ≤ weights j code)
    (label : Fin (raw n sizes bids weights hb hw).labels) :
    (raw n sizes bids weights hb hw).weight label =
      SparseMW.productMass weights (labelEquiv n sizes bids weights hb hw label) := by
  induction n with
  | zero =>
      simp [raw, ProductBidTree.weight, SparseMW.productMass, labelEquiv, oneFieldEquiv, fieldFamily]
      rfl
  | succ n ih =>
      change weights 0 (finProdFinEquiv.symm label).1 *
        (raw n _ _ _ _ _).weight (finProdFinEquiv.symm label).2 = _
      rw [ih]
      unfold SparseMW.productMass
      conv_rhs => rw [Fin.prod_univ_succ]
      rfl

theorem raw_resource (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 ≤ weights j code)
    (label : Fin (raw n sizes bids weights hb hw).labels) :
    (raw n sizes bids weights hb hw).resource label =
      SparseMW.productResource bids (labelEquiv n sizes bids weights hb hw label) := by
  induction n with
  | zero =>
      simp [raw, ProductBidTree.resource, SparseMW.productResource, labelEquiv, oneFieldEquiv, fieldFamily]
      rfl
  | succ n ih =>
      change bids 0 (finProdFinEquiv.symm label).1 +
        (raw n _ _ _ _ _).resource (finProdFinEquiv.symm label).2 = _
      rw [ih]
      unfold SparseMW.productResource
      conv_rhs => rw [Fin.sum_univ_succ]
      rfl

theorem raw_decode (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 ≤ weights j code)
    (label : Fin (raw n sizes bids weights hb hw).labels) (field : Fin (n + 1)) :
    (raw n sizes bids weights hb hw).decode label (field.cast (raw_fields n sizes bids weights hb hw).symm) =
      bids field (labelEquiv n sizes bids weights hb hw label field) := by
  induction n with
  | zero =>
      fin_cases field
      rfl
  | succ n ih =>
      refine Fin.cases ?_ ?_ field
      · change Fin.addCases (motive := fun _ => ℚ)
          (fun _ : Fin 1 => bids 0 (finProdFinEquiv.symm label).1)
          ((raw n _ _ _ _ _).decode (finProdFinEquiv.symm label).2) _ = _
        have hField : (0 : Fin ((n + 1) + 1)).cast
            (raw_fields (n + 1) sizes bids weights hb hw).symm =
          Fin.castAdd (raw n (fun j => sizes j.succ) (fun j => bids j.succ) (fun j => weights j.succ)
            (fun j => hb j.succ) (fun j => hw j.succ)).fields (0 : Fin 1) := Fin.ext rfl
        rw [hField, Fin.addCases_left]
        rfl
      · intro j
        let tail := raw n (fun j => sizes j.succ) (fun j => bids j.succ) (fun j => weights j.succ)
          (fun j => hb j.succ) (fun j => hw j.succ)
        have hField : j.succ.cast (raw_fields (n + 1) sizes bids weights hb hw).symm =
            Fin.natAdd 1 (j.cast (raw_fields n _ _ _ _ _).symm) := by
          apply Fin.ext
          simp only [Fin.val_cast, Fin.val_succ, Fin.val_natAdd]
          omega
        change Fin.addCases (motive := fun _ => ℚ)
          (fun _ : Fin 1 => bids 0 (finProdFinEquiv.symm label).1)
          (tail.decode (finProdFinEquiv.symm label).2) _ = _
        rw [hField, Fin.addCases_right]
        exact ih _ _ _ _ _ (finProdFinEquiv.symm label).2 j

def constructed (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 ≤ weights j code) : ProductBidTree :=
  (raw n sizes bids weights hb hw).constructGuides

theorem constructed_certified (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 ≤ weights j code) :
    (constructed n sizes bids weights hb hw).guideTree.real.LowerCertified :=
  (raw n sizes bids weights hb hw).constructGuides_certified

theorem constructed_fields (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 ≤ weights j code) :
    (constructed n sizes bids weights hb hw).fields = n + 1 :=
  ((raw n sizes bids weights hb hw).rebuild_fields _).trans (raw_fields n sizes bids weights hb hw)

theorem rebuild_weight (tree : ProductBidTree) (gamma : ℚ) (label : Fin tree.labels) :
    (tree.rebuildGuides gamma).weight (label.cast (tree.rebuild_labels gamma).symm) = tree.weight label := by
  induction tree with
  | leaf family hn guide g => rfl
  | fork guide g left right ihL ihR =>
      let pair := finProdFinEquiv.symm label
      have hp : label.cast ((ProductBidTree.fork guide g left right).rebuild_labels gamma).symm =
          finProdFinEquiv
            (pair.1.cast (left.rebuild_labels gamma).symm, pair.2.cast (right.rebuild_labels gamma).symm) := by
        apply Fin.ext
        have he := congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv label)
        simp only [finProdFinEquiv_apply_val, Fin.val_cast] at he ⊢
        rw [right.rebuild_labels gamma]
        exact he.symm
      change (left.rebuildGuides gamma).weight (finProdFinEquiv.symm _).1 *
        (right.rebuildGuides gamma).weight (finProdFinEquiv.symm _).2 = left.weight pair.1 * right.weight pair.2
      rw [hp, Equiv.symm_apply_apply, ihL, ihR]

def finCastEquiv {a b : ℕ} (h : a = b) : Fin a ≃ Fin b where
  toFun := fun j => j.cast h
  invFun := fun j => j.cast h.symm
  left_inv := fun _ => Fin.ext rfl
  right_inv := fun _ => Fin.ext rfl

def constructedLabelEquiv (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 ≤ weights j code) :
    Fin (constructed n sizes bids weights hb hw).labels ≃ SparseMW.ProductCodes sizes :=
  (finCastEquiv ((raw n sizes bids weights hb hw).rebuild_labels _)).trans
    (labelEquiv n sizes bids weights hb hw)

theorem constructed_resource (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 ≤ weights j code)
    (label : Fin (constructed n sizes bids weights hb hw).labels) :
    (constructed n sizes bids weights hb hw).resource label =
      SparseMW.productResource bids (constructedLabelEquiv n sizes bids weights hb hw label) := by
  let original := label.cast ((raw n sizes bids weights hb hw).rebuild_labels _)
  have h := (raw n sizes bids weights hb hw).rebuild_resource
    (raw n sizes bids weights hb hw).constructionGamma original
  have hi : original.cast ((raw n sizes bids weights hb hw).rebuild_labels _).symm = label := Fin.ext rfl
  rw [hi] at h
  exact h.trans (raw_resource n sizes bids weights hb hw original)

theorem constructed_weight (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 ≤ weights j code)
    (label : Fin (constructed n sizes bids weights hb hw).labels) :
    (constructed n sizes bids weights hb hw).weight label =
      SparseMW.productMass weights (constructedLabelEquiv n sizes bids weights hb hw label) := by
  let original := label.cast ((raw n sizes bids weights hb hw).rebuild_labels _)
  have h := rebuild_weight (raw n sizes bids weights hb hw)
    (raw n sizes bids weights hb hw).constructionGamma original
  have hi : original.cast ((raw n sizes bids weights hb hw).rebuild_labels _).symm = label := Fin.ext rfl
  rw [hi] at h
  exact h.trans (raw_weight n sizes bids weights hb hw original)

theorem constructed_decode (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 ≤ weights j code)
    (label : Fin (constructed n sizes bids weights hb hw).labels) (field : Fin (n + 1)) :
    (constructed n sizes bids weights hb hw).decode label
      (field.cast (constructed_fields n sizes bids weights hb hw).symm) =
        bids field (constructedLabelEquiv n sizes bids weights hb hw label field) := by
  let original := label.cast ((raw n sizes bids weights hb hw).rebuild_labels _)
  let rawField := field.cast (raw_fields n sizes bids weights hb hw).symm
  have h := (raw n sizes bids weights hb hw).rebuild_decode
    (raw n sizes bids weights hb hw).constructionGamma original rawField
  have hi : original.cast ((raw n sizes bids weights hb hw).rebuild_labels _).symm = label := Fin.ext rfl
  have hj : rawField.cast ((raw n sizes bids weights hb hw).rebuild_fields _).symm =
      field.cast (constructed_fields n sizes bids weights hb hw).symm := Fin.ext rfl
  rw [hi, hj] at h
  exact h.trans (raw_decode n sizes bids weights hb hw original field)

end ProductArrayTree
end Blotto
