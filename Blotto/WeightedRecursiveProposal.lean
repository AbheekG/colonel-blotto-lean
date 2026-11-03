import Blotto.WeightedProposalStep

/-! Actual finite augmented records and recursive R160 proposal semantics.
Records with infeasible leaf choices have probability zero. Importance on
impossible records is not asserted positive. No execution cost is claimed. -/

namespace Blotto
open scoped BigOperators Classical

namespace WeightedGuideTree

def ProposalRecord : WeightedGuideTree → Type
  | .leaf (n := n) _ _ _ => Fin n
  | .fork _ _ left right => Fin left.guideSize × right.ProposalRecord × left.ProposalRecord

@[reducible] noncomputable def recordFintype : (tree : WeightedGuideTree) → Fintype tree.ProposalRecord
  | .leaf (n := n) _ _ _ => Fin.fintype n
  | .fork _ _ left right =>
      @instFintypeProd _ _ (inferInstance : Fintype (Fin left.guideSize))
        (@instFintypeProd _ _ right.recordFintype left.recordFintype)

attribute [instance] recordFintype

noncomputable def proposalOutput : (tree : WeightedGuideTree) → tree.ProposalRecord → Fin tree.trueSize
  | .leaf _ _ _, i => i
  | .fork _ _ left right, record =>
      finProdFinEquiv (left.proposalOutput record.2.2, right.proposalOutput record.2.1)

noncomputable def proposalResource (tree : WeightedGuideTree) (record : tree.ProposalRecord) : ℝ :=
  tree.trueFamily.resource (tree.proposalOutput record)

noncomputable def proposalWeight (tree : WeightedGuideTree) (record : tree.ProposalRecord) : ℝ :=
  tree.trueFamily.mass (tree.proposalOutput record)

noncomputable def proposalProbability : (tree : WeightedGuideTree) → ℝ → tree.ProposalRecord → ℝ
  | .leaf family _ _, B, i => family.auxiliaryChoice B i
  | .fork _ _ left right, B, record =>
      let i := record.1
      let r := record.2.1
      let l := record.2.2
      left.guide.syntheticChoice right.guide B i *
        right.proposalProbability (B - left.guide.resource i) r *
        left.proposalProbability (B - right.proposalResource r) l

noncomputable def proposalImportance : (tree : WeightedGuideTree) → ℝ → tree.ProposalRecord → ℝ
  | .leaf family _ _, B, _ => family.prefixMass B
  | .fork _ _ left right, B, record =>
      let i := record.1
      let r := record.2.1
      let l := record.2.2
      WeightedProposalStep.importance (left.guide.convolution right.guide B)
        (left.proposalImportance (B - right.proposalResource r) l)
        (right.proposalImportance (B - left.guide.resource i) r)
        (left.guide.prefixMass (B - right.proposalResource r))
        (right.guide.prefixMass (B - left.guide.resource i))

noncomputable def proposalAuxiliary : (tree : WeightedGuideTree) → ℝ → tree.ProposalRecord → ℝ
  | .leaf family _ _, B, i => if family.resource i ≤ B then 1 else 0
  | .fork _ _ left right, B, record =>
      let i := record.1
      let r := record.2.1
      let l := record.2.2
      left.guide.auxiliaryChoice (B - right.proposalResource r) i *
        right.proposalAuxiliary (B - left.guide.resource i) r *
        left.proposalAuxiliary (B - right.proposalResource r) l

theorem proposalResource_fork {p : ℕ} (guide : WeightedResourceFamily p) (gamma : ℝ)
    (left right : WeightedGuideTree)
    (record : (fork guide gamma left right).ProposalRecord) :
    (fork guide gamma left right).proposalResource record =
      left.proposalResource record.2.2 + right.proposalResource record.2.1 := by
  exact left.trueFamily.product_resource right.trueFamily _ _

theorem proposalWeight_fork {p : ℕ} (guide : WeightedResourceFamily p) (gamma : ℝ)
    (left right : WeightedGuideTree)
    (record : (fork guide gamma left right).ProposalRecord) :
    (fork guide gamma left right).proposalWeight record =
      left.proposalWeight record.2.2 * right.proposalWeight record.2.1 := by
  exact left.trueFamily.product_mass right.trueFamily _ _

theorem proposalProbability_nonnegative (tree : WeightedGuideTree) (B : ℝ)
    (record : tree.ProposalRecord) : 0 ≤ tree.proposalProbability B record := by
  induction tree generalizing B with
  | leaf family guide gamma => exact family.auxiliaryChoice_nonnegative B record
  | fork guide gamma left right ihLeft ihRight =>
    exact mul_nonneg
      (mul_nonneg (left.guide.syntheticChoice_nonnegative right.guide B record.1)
        (ihRight _ record.2.1)) (ihLeft _ record.2.2)

theorem proposalImportance_nonnegative (tree : WeightedGuideTree) (B : ℝ)
    (record : tree.ProposalRecord) : 0 ≤ tree.proposalImportance B record := by
  induction tree generalizing B with
  | leaf family guide gamma => exact family.prefix_nonnegative B
  | fork guide gamma left right ihLeft ihRight =>
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (left.guide.convolution_nonnegative right.guide B) (ihLeft _ record.2.2))
        (ihRight _ record.2.1))
      (mul_nonneg (left.guide.prefix_nonnegative _) (right.guide.prefix_nonnegative _))

theorem proposalAuxiliary_nonnegative (tree : WeightedGuideTree) (B : ℝ)
    (record : tree.ProposalRecord) : 0 ≤ tree.proposalAuxiliary B record := by
  induction tree generalizing B with
  | leaf family guide gamma =>
    change 0 ≤ if family.resource record ≤ B then (1 : ℝ) else 0
    split_ifs <;> norm_num
  | fork guide gamma left right ihLeft ihRight =>
    exact mul_nonneg
      (mul_nonneg (left.guide.auxiliaryChoice_nonnegative _ record.1)
        (ihRight _ record.2.1)) (ihLeft _ record.2.2)

theorem proposalProbability_leaf_sum {n p : ℕ} (family : WeightedResourceFamily n)
    (guide : WeightedResourceFamily p) (gamma B : ℝ) (h : 0 < family.prefixMass B) :
    ∑ record : (leaf family guide gamma).ProposalRecord,
      (leaf family guide gamma).proposalProbability B record = 1 :=
  family.auxiliaryChoice_sum B h

theorem proposal_leaf_identity {n p : ℕ} (family : WeightedResourceFamily n)
    (guide : WeightedResourceFamily p) (gamma B : ℝ) (h : 0 < family.prefixMass B)
    (record : (leaf family guide gamma).ProposalRecord) :
    (leaf family guide gamma).proposalProbability B record *
        (leaf family guide gamma).proposalImportance B record =
      (leaf family guide gamma).proposalWeight record *
        (leaf family guide gamma).proposalAuxiliary B record := by
  change (if family.resource record ≤ B then family.mass record / family.prefixMass B else 0) *
      family.prefixMass B = family.mass record * (if family.resource record ≤ B then 1 else 0)
  split_ifs
  · simp [ne_of_gt h]
  · simp

theorem positive_product_factors {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : 0 < x * y) : 0 < x ∧ 0 < y := by
  constructor
  · by_contra hn
    have he : x = 0 := le_antisymm (le_of_not_gt hn) hx
    simp only [he, zero_mul, lt_self_iff_false] at h
  · by_contra hn
    have he : y = 0 := le_antisymm (le_of_not_gt hn) hy
    simp only [he, mul_zero, lt_self_iff_false] at h

theorem proposal_positive_contract (tree : WeightedGuideTree) (h : tree.LowerCertified)
    (B : ℝ) (record : tree.ProposalRecord)
    (hq : 0 < tree.proposalProbability B record) :
    tree.proposalResource record ≤ B ∧ 0 < tree.proposalWeight record ∧
      0 < tree.proposalImportance B record ∧
      tree.proposalImportance B record / tree.guide.prefixMass B ≤ tree.factor := by
  induction tree generalizing B with
  | leaf family guide gamma =>
    have hr : family.resource record ≤ B := by
      by_contra hn
      simp only [proposalProbability, WeightedResourceFamily.auxiliaryChoice,
        hn, ite_false, lt_self_iff_false] at hq
    have hm : 0 < family.mass record := by
      have hm0 := family.mass_nonnegative record
      by_contra hn
      have hz : family.mass record = 0 := le_antisymm (le_of_not_gt hn) hm0
      simp only [proposalProbability, WeightedResourceFamily.auxiliaryChoice,
        hr, ite_true, hz, zero_div, lt_self_iff_false] at hq
    have hf := family.selected_prefix_positive record B hr hm
    have hg := ((leaf family guide gamma).prefix_positive_iff h B).mpr hf
    refine ⟨hr, hm, hf, ?_⟩
    change family.prefixMass B / guide.prefixMass B ≤ gamma
    exact (div_le_iff₀ hg).mpr ((h.2 B).2)
  | fork guide gamma left right ihLeft ihRight =>
    let i := record.1
    let r := record.2.1
    let l := record.2.2
    let s := left.guide.syntheticChoice right.guide B i
    let qr := right.proposalProbability (B - left.guide.resource i) r
    let ql := left.proposalProbability (B - right.proposalResource r) l
    have hs0 : 0 ≤ s := left.guide.syntheticChoice_nonnegative right.guide B i
    have hqr0 : 0 ≤ qr := right.proposalProbability_nonnegative _ r
    have hql0 : 0 ≤ ql := left.proposalProbability_nonnegative _ l
    change 0 < s * qr * ql at hq
    have hpair := positive_product_factors (mul_nonneg hs0 hqr0) hql0 hq
    have hfirst := positive_product_factors hs0 hqr0 hpair.1
    have hselected : 0 < left.guide.mass i * right.guide.prefixMass (B - left.guide.resource i) := by
      by_contra hn
      have hz : left.guide.mass i * right.guide.prefixMass (B - left.guide.resource i) = 0 :=
        le_antisymm (le_of_not_gt hn)
          (mul_nonneg (left.guide.mass_nonnegative i) (right.guide.prefix_nonnegative _))
      simp only [s, WeightedResourceFamily.syntheticChoice, hz, zero_div, lt_self_iff_false] at hfirst
      exact hfirst.1
    have hr := ihRight h.2.2.1 _ r hfirst.2
    have hl := ihLeft h.2.1 _ l hpair.2
    have hc := WeightedProposalStep.selected_fork_contract left.guide right.guide i B
      (left.proposalResource l) (right.proposalResource r)
      (left.proposalImportance (B - right.proposalResource r) l)
      (right.proposalImportance (B - left.guide.resource i) r)
      left.factor right.factor hselected hr.1 hl.1 hl.2.2.1 hr.2.2.1
      (left.factor_nonnegative h.2.1) hl.2.2.2 hr.2.2.2
    dsimp only at hc
    have hresource : (fork guide gamma left right).proposalResource record ≤ B := by
      rw [proposalResource_fork]
      exact hc.2.2.2.1
    have hweight : 0 < (fork guide gamma left right).proposalWeight record := by
      rw [proposalWeight_fork]
      exact mul_pos hl.2.1 hr.2.1
    have hguide := ((fork guide gamma left right).prefix_positive_iff h B).mpr
      (((fork guide gamma left right).trueFamily.prefix_positive_iff_exists B).mpr
        ⟨(fork guide gamma left right).proposalOutput record, hresource, hweight⟩)
    refine ⟨hresource, hweight, hc.2.2.2.2.1, ?_⟩
    have hb := WeightedProposalStep.parent_guide_ratio_bound hguide
      (left.factor_nonnegative h.2.1) (right.factor_nonnegative h.2.2.1)
      hc.2.2.2.2.2 ((h.2.2.2 B).2)
    change WeightedProposalStep.importance (left.guide.convolution right.guide B)
      (left.proposalImportance (B - right.proposalResource r) l)
      (right.proposalImportance (B - left.guide.resource i) r)
      (left.guide.prefixMass (B - right.proposalResource r))
      (right.guide.prefixMass (B - left.guide.resource i)) /
      (fork guide gamma left right).guide.prefixMass B ≤ left.factor * right.factor * gamma
    convert hb using 1
    ring

theorem proposalProbability_sum (tree : WeightedGuideTree) (h : tree.LowerCertified)
    (B : ℝ) (hB : 0 < tree.trueFamily.prefixMass B) :
    ∑ record : tree.ProposalRecord, tree.proposalProbability B record = 1 := by
  induction tree generalizing B with
  | leaf family guide gamma => exact family.auxiliaryChoice_sum B hB
  | fork guide gamma left right ihLeft ihRight =>
    change 0 < (left.trueFamily.product right.trueFamily).prefixMass B at hB
    rw [WeightedResourceFamily.product_prefix] at hB
    have hZ := (root_synthetic_positive_iff left right h.2.1 h.2.2.1 B).mpr
      hB
    change (∑ record : Fin left.guideSize × right.ProposalRecord × left.ProposalRecord,
      left.guide.syntheticChoice right.guide B record.1 *
        right.proposalProbability (B - left.guide.resource record.1) record.2.1 *
        left.proposalProbability (B - right.proposalResource record.2.1) record.2.2) = 1
    rw [Fintype.sum_prod_type]
    have hi : ∀ i : Fin left.guideSize,
        (∑ record : right.ProposalRecord × left.ProposalRecord,
          left.guide.syntheticChoice right.guide B i *
            right.proposalProbability (B - left.guide.resource i) record.1 *
            left.proposalProbability (B - right.proposalResource record.1) record.2) =
          left.guide.syntheticChoice right.guide B i := by
      intro i
      rw [Fintype.sum_prod_type]
      by_cases hs : left.guide.syntheticChoice right.guide B i = 0
      · simp [hs]
      have hsPos : 0 < left.guide.syntheticChoice right.guide B i :=
        lt_of_le_of_ne (left.guide.syntheticChoice_nonnegative right.guide B i) (Ne.symm hs)
      have hselected : 0 < left.guide.mass i * right.guide.prefixMass (B - left.guide.resource i) := by
        by_contra hn
        have hz : left.guide.mass i * right.guide.prefixMass (B - left.guide.resource i) = 0 :=
          le_antisymm (le_of_not_gt hn)
            (mul_nonneg (left.guide.mass_nonnegative i) (right.guide.prefix_nonnegative _))
        simp only [WeightedResourceFamily.syntheticChoice, hz, zero_div, lt_self_iff_false] at hsPos
      have hden : 0 < right.guide.prefixMass (B - left.guide.resource i) := by
        by_contra hn
        have hz : right.guide.prefixMass (B - left.guide.resource i) = 0 :=
          le_antisymm (le_of_not_gt hn) (right.guide.prefix_nonnegative _)
        simp only [hz, mul_zero, lt_self_iff_false] at hselected
      have hrSum := ihRight h.2.2.1 (B - left.guide.resource i)
        ((right.prefix_positive_iff h.2.2.1 _).mp hden)
      have hrTerms : ∀ r : right.ProposalRecord,
          (∑ l : left.ProposalRecord,
            left.guide.syntheticChoice right.guide B i *
              right.proposalProbability (B - left.guide.resource i) r *
              left.proposalProbability (B - right.proposalResource r) l) =
            left.guide.syntheticChoice right.guide B i *
              right.proposalProbability (B - left.guide.resource i) r := by
        intro r
        rw [← Finset.mul_sum]
        by_cases hrZero : right.proposalProbability (B - left.guide.resource i) r = 0
        · simp only [hrZero, mul_zero, zero_mul]
        have hrPos : 0 < right.proposalProbability (B - left.guide.resource i) r :=
          lt_of_le_of_ne (right.proposalProbability_nonnegative _ r) (Ne.symm hrZero)
        have hrContract := right.proposal_positive_contract h.2.2.1 _ r hrPos
        have hd := WeightedProposalStep.selected_denominators_positive
          left.guide right.guide i B (right.proposalResource r) hselected hrContract.1
        have hlSum := ihLeft h.2.1 (B - right.proposalResource r)
          ((left.prefix_positive_iff h.2.1 _).mp hd.2)
        rw [hlSum, mul_one]
      simp_rw [hrTerms]
      rw [← Finset.mul_sum, hrSum, mul_one]
    simp_rw [hi]
    exact left.guide.syntheticChoice_sum right.guide B hZ

end WeightedGuideTree
end Blotto
