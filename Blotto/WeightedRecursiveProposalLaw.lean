import Blotto.WeightedRecursiveProposal

/-! Augmented-record law identities for the actual recursive R160 proposal.
Auxiliary statements restrict to feasible positive-weight true outputs. -/

namespace Blotto
open scoped BigOperators Classical

namespace WeightedGuideTree

theorem proposalAuxiliary_positive_support (tree : WeightedGuideTree) (B : ℝ)
    (record : tree.ProposalRecord) (h : 0 < tree.proposalAuxiliary B record) :
    tree.proposalResource record ≤ B := by
  induction tree generalizing B with
  | leaf family guide gamma =>
    change family.resource record ≤ B
    by_contra hn
    simp only [proposalAuxiliary, hn, ite_false, lt_self_iff_false] at h
  | fork guide gamma left right ihLeft ihRight =>
    have hp := positive_product_factors
      (mul_nonneg (left.guide.auxiliaryChoice_nonnegative _ record.1)
        (right.proposalAuxiliary_nonnegative _ record.2.1))
      (left.proposalAuxiliary_nonnegative _ record.2.2) h
    have hl := ihLeft _ record.2.2 hp.2
    rw [proposalResource_fork]
    linarith

theorem proposalAuxiliary_weight_positive_probability (tree : WeightedGuideTree)
    (hc : tree.LowerCertified) (B : ℝ) (record : tree.ProposalRecord)
    (hw : 0 < tree.proposalWeight record) (ha : 0 < tree.proposalAuxiliary B record) :
    0 < tree.proposalProbability B record := by
  induction tree generalizing B with
  | leaf family guide gamma =>
    have hr := (leaf family guide gamma).proposalAuxiliary_positive_support B record ha
    change family.resource record ≤ B at hr
    have hf := family.selected_prefix_positive record B hr hw
    change 0 < if family.resource record ≤ B then family.mass record / family.prefixMass B else 0
    rw [ite_eq_left hr]
    exact div_pos hw hf
  | fork guide gamma left right ihLeft ihRight =>
    let i := record.1
    let r := record.2.1
    let l := record.2.2
    rw [proposalWeight_fork] at hw
    have hwLeft : 0 ≤ left.proposalWeight l := left.trueFamily.mass_nonnegative _
    have hwRight : 0 ≤ right.proposalWeight r := right.trueFamily.mass_nonnegative _
    have hwPair := positive_product_factors hwLeft hwRight hw
    have haPair := positive_product_factors
      (mul_nonneg (left.guide.auxiliaryChoice_nonnegative _ i)
        (right.proposalAuxiliary_nonnegative _ r))
      (left.proposalAuxiliary_nonnegative _ l) ha
    have haFirst := positive_product_factors (left.guide.auxiliaryChoice_nonnegative _ i)
      (right.proposalAuxiliary_nonnegative _ r) haPair.1
    have hqr := ihRight hc.2.2.1 _ r hwPair.2 haFirst.2
    have hql := ihLeft hc.2.1 _ l hwPair.1 haPair.2
    have hright := right.proposal_positive_contract hc.2.2.1 _ r hqr
    have hrightGuide := (right.prefix_positive_iff hc.2.2.1 _).mpr
      (right.trueFamily.selected_prefix_positive (right.proposalOutput r) _ hright.1 hright.2.1)
    have hmass : 0 < left.guide.mass i := by
      by_contra hn
      have hz : left.guide.mass i = 0 :=
        le_antisymm (le_of_not_gt hn) (left.guide.mass_nonnegative i)
      simp only [WeightedResourceFamily.auxiliaryChoice, hz, zero_div,
        ite_self, lt_self_iff_false] at haFirst
      exact haFirst.1
    have hselected : 0 < left.guide.mass i * right.guide.prefixMass (B - left.guide.resource i) :=
      mul_pos hmass hrightGuide
    have hZ := left.guide.selected_convolution_positive right.guide i B hselected
    have hs : 0 < left.guide.syntheticChoice right.guide B i := div_pos hselected hZ
    exact mul_pos (mul_pos hs hqr) hql

theorem proposal_pointwise_identity_on_positive (tree : WeightedGuideTree)
    (hc : tree.LowerCertified) (B : ℝ) (record : tree.ProposalRecord)
    (hq : 0 < tree.proposalProbability B record) :
    tree.proposalProbability B record * tree.proposalImportance B record =
      tree.proposalWeight record * tree.proposalAuxiliary B record := by
  induction tree generalizing B with
  | leaf family guide gamma =>
    have hp := (leaf family guide gamma).proposal_positive_contract hc B record hq
    have hf := family.selected_prefix_positive record B hp.1 hp.2.1
    exact proposal_leaf_identity family guide gamma B hf record
  | fork guide gamma left right ihLeft ihRight =>
    let i := record.1
    let r := record.2.1
    let l := record.2.2
    have hp := positive_product_factors
      (mul_nonneg (left.guide.syntheticChoice_nonnegative right.guide B i)
        (right.proposalProbability_nonnegative _ r))
      (left.proposalProbability_nonnegative _ l) hq
    have hf := positive_product_factors (left.guide.syntheticChoice_nonnegative right.guide B i)
      (right.proposalProbability_nonnegative _ r) hp.1
    have hr := right.proposal_positive_contract hc.2.2.1 _ r hf.2
    have hselected : 0 < left.guide.mass i * right.guide.prefixMass (B - left.guide.resource i) := by
      by_contra hn
      have hz : left.guide.mass i * right.guide.prefixMass (B - left.guide.resource i) = 0 :=
        le_antisymm (le_of_not_gt hn)
          (mul_nonneg (left.guide.mass_nonnegative i) (right.guide.prefix_nonnegative _))
      simp only [WeightedResourceFamily.syntheticChoice, hz, zero_div, lt_self_iff_false] at hf
      exact hf.1
    have he := WeightedProposalStep.selected_path_cancellation left.guide right.guide i
      B (right.proposalResource r)
      (left.proposalProbability (B - right.proposalResource r) l)
      (right.proposalProbability (B - left.guide.resource i) r)
      (left.proposalImportance (B - right.proposalResource r) l)
      (right.proposalImportance (B - left.guide.resource i) r)
      (left.proposalWeight l) (right.proposalWeight r)
      (left.proposalAuxiliary (B - right.proposalResource r) l)
      (right.proposalAuxiliary (B - left.guide.resource i) r)
      hselected hr.1 (ihLeft hc.2.1 _ l hp.2) (ihRight hc.2.2.1 _ r hf.2)
    have hy : left.guide.resource i ≤ B - right.proposalResource r := by linarith [hr.1]
    rw [proposalWeight_fork]
    change _ = (left.proposalWeight l * right.proposalWeight r) *
      (left.guide.auxiliaryChoice (B - right.proposalResource r) i *
        right.proposalAuxiliary (B - left.guide.resource i) r *
        left.proposalAuxiliary (B - right.proposalResource r) l)
    simpa only [WeightedProposalStep.pathProbability, WeightedProposalStep.auxiliaryPath,
      proposalProbability, proposalImportance, WeightedResourceFamily.syntheticChoice,
      WeightedResourceFamily.auxiliaryChoice, hy, ite_true] using he

theorem proposal_pointwise_identity (tree : WeightedGuideTree) (hc : tree.LowerCertified)
    (B : ℝ) (record : tree.ProposalRecord) :
    tree.proposalProbability B record * tree.proposalImportance B record =
      tree.proposalWeight record * tree.proposalAuxiliary B record := by
  by_cases hq : tree.proposalProbability B record = 0
  · have hr : tree.proposalWeight record * tree.proposalAuxiliary B record = 0 := by
      by_contra hn
      have hp : 0 < tree.proposalWeight record * tree.proposalAuxiliary B record :=
        lt_of_le_of_ne
          (mul_nonneg (tree.trueFamily.mass_nonnegative _) (tree.proposalAuxiliary_nonnegative B record))
          (Ne.symm hn)
      have hf := positive_product_factors (tree.trueFamily.mass_nonnegative _)
        (tree.proposalAuxiliary_nonnegative B record) hp
      have he := tree.proposalAuxiliary_weight_positive_probability hc B record hf.1 hf.2
      simp only [hq, lt_self_iff_false] at he
    simp only [hq, zero_mul, hr]
  · exact proposal_pointwise_identity_on_positive tree hc B record
      (lt_of_le_of_ne (tree.proposalProbability_nonnegative B record) (Ne.symm hq))

noncomputable def auxiliaryFiber (tree : WeightedGuideTree) (B : ℝ)
    (label : Fin tree.trueSize) : ℝ :=
  ∑ record : tree.ProposalRecord,
    if tree.proposalOutput record = label then tree.proposalAuxiliary B record else 0

theorem auxiliaryFiber_leaf {n p : ℕ} (family : WeightedResourceFamily n)
    (guide : WeightedResourceFamily p) (gamma B : ℝ) (label : Fin n) :
    (leaf family guide gamma).auxiliaryFiber B label =
      if family.resource label ≤ B then 1 else 0 := by
  change (∑ record : Fin n,
    if record = label then (if family.resource record ≤ B then (1 : ℝ) else 0) else 0) = _
  simp

theorem auxiliaryFiber_fork {p : ℕ} (guide : WeightedResourceFamily p) (gamma : ℝ)
    (left right : WeightedGuideTree) (B : ℝ)
    (labelLeft : Fin left.trueSize) (labelRight : Fin right.trueSize) :
    (fork guide gamma left right).auxiliaryFiber B (finProdFinEquiv (labelLeft, labelRight)) =
      ∑ i : Fin left.guideSize,
        left.guide.auxiliaryChoice (B - right.trueFamily.resource labelRight) i *
          right.auxiliaryFiber (B - left.guide.resource i) labelRight *
          left.auxiliaryFiber (B - right.trueFamily.resource labelRight) labelLeft := by
  change (∑ record : Fin left.guideSize × right.ProposalRecord × left.ProposalRecord,
    if finProdFinEquiv (left.proposalOutput record.2.2, right.proposalOutput record.2.1) =
        finProdFinEquiv (labelLeft, labelRight)
    then left.guide.auxiliaryChoice (B - right.proposalResource record.2.1) record.1 *
      right.proposalAuxiliary (B - left.guide.resource record.1) record.2.1 *
      left.proposalAuxiliary (B - right.proposalResource record.2.1) record.2.2 else 0) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]
  unfold auxiliaryFiber
  rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro l _
  have he : finProdFinEquiv (left.proposalOutput l, right.proposalOutput r) =
      finProdFinEquiv (labelLeft, labelRight) ↔
      left.proposalOutput l = labelLeft ∧ right.proposalOutput r = labelRight := by
    rw [Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hr : right.proposalOutput r = labelRight
  · have hresource : right.proposalResource r = right.trueFamily.resource labelRight := by
      unfold proposalResource
      rw [hr]
    by_cases hl : left.proposalOutput l = labelLeft
    · have hp := he.mpr ⟨hl, hr⟩
      rw [ite_eq_left hp, ite_eq_left hr, ite_eq_left hl, hresource]
    · have hp : ¬finProdFinEquiv (left.proposalOutput l, right.proposalOutput r) =
          finProdFinEquiv (labelLeft, labelRight) := fun hp => hl (he.mp hp).1
      rw [ite_eq_right hp, ite_eq_right hl, mul_zero]
  · have hp : ¬finProdFinEquiv (left.proposalOutput l, right.proposalOutput r) =
        finProdFinEquiv (labelLeft, labelRight) := fun hp => hr (he.mp hp).2
    rw [ite_eq_right hp, ite_eq_right hr, mul_zero, zero_mul]

theorem auxiliaryFiber_normalized (tree : WeightedGuideTree) (hc : tree.LowerCertified)
    (B : ℝ) (label : Fin tree.trueSize) (hresource : tree.trueFamily.resource label ≤ B)
    (hweight : 0 < tree.trueFamily.mass label) : tree.auxiliaryFiber B label = 1 := by
  induction tree generalizing B with
  | leaf family guide gamma =>
    change family.resource label ≤ B at hresource
    have he := auxiliaryFiber_leaf family guide gamma B (label : Fin _)
    rw [he]
    exact ite_eq_left hresource
  | fork guide gamma left right ihLeft ihRight =>
    let pair := finProdFinEquiv.symm label
    have hlabel : finProdFinEquiv pair = label := Equiv.apply_symm_apply _ _
    have hresourcePair : left.trueFamily.resource pair.1 + right.trueFamily.resource pair.2 ≤ B := by
      change (left.trueFamily.product right.trueFamily).resource label ≤ B at hresource
      rw [← hlabel, WeightedResourceFamily.product_resource] at hresource
      exact hresource
    have hweightPair : 0 < left.trueFamily.mass pair.1 * right.trueFamily.mass pair.2 := by
      change 0 < (left.trueFamily.product right.trueFamily).mass label at hweight
      rw [← hlabel, WeightedResourceFamily.product_mass] at hweight
      exact hweight
    have hw := positive_product_factors (left.trueFamily.mass_nonnegative pair.1)
      (right.trueFamily.mass_nonnegative pair.2) hweightPair
    have hleftResource : left.trueFamily.resource pair.1 ≤ B - right.trueFamily.resource pair.2 := by
      linarith
    have hleftPrefix := left.trueFamily.selected_prefix_positive pair.1 _ hleftResource hw.1
    have hleftGuide := (left.prefix_positive_iff hc.2.1 _).mpr hleftPrefix
    rw [← hlabel, auxiliaryFiber_fork]
    have hleftFiber := ihLeft hc.2.1 _ pair.1 hleftResource hw.1
    have hterms : ∀ i : Fin left.guideSize,
        left.guide.auxiliaryChoice (B - right.trueFamily.resource pair.2) i *
          right.auxiliaryFiber (B - left.guide.resource i) pair.2 *
          left.auxiliaryFiber (B - right.trueFamily.resource pair.2) pair.1 =
        left.guide.auxiliaryChoice (B - right.trueFamily.resource pair.2) i := by
      intro i
      by_cases hi : left.guide.resource i ≤ B - right.trueFamily.resource pair.2
      · have hrightResource : right.trueFamily.resource pair.2 ≤ B - left.guide.resource i := by
          linarith
        rw [ihRight hc.2.2.1 _ pair.2 hrightResource hw.2, hleftFiber, mul_one, mul_one]
      · simp only [WeightedResourceFamily.auxiliaryChoice, hi, ite_false, zero_mul]
    calc
      _ = ∑ i : Fin left.guideSize,
          left.guide.auxiliaryChoice (B - right.trueFamily.resource pair.2) i := by
            apply Finset.sum_congr rfl
            intro i _
            exact hterms i
      _ = 1 := left.guide.auxiliaryChoice_sum _ hleftGuide

end WeightedGuideTree
end Blotto
