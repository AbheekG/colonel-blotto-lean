import Blotto.RoundedImplicitTree
import Blotto.ProductArrayTreeLaw

/-! Original Cartesian labels of succinct rounded leaf trees realize the
current constrained product Gibbs law. Every local code is retained, including
duplicate resources. Cartesian sums and equivalences occur in proofs only. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts

def leafCombLabelEquiv : (n : ℕ) → (data : Fin (n + 1) → ProposalLeaf) →
    Fin (leafComb n data).projected.trueSize ≃ SparseMW.ProductCodes (fun field => (data field).cap + 1)
  | 0, data => (ProductArrayTree.oneFieldEquiv (fun field => (data field).cap + 1)).symm
  | n + 1, data => finProdFinEquiv.symm |>.trans
      ((Equiv.prodCongr (Equiv.refl _) (leafCombLabelEquiv n (fun field => data field.succ))).trans
        (ProductArrayTree.headTailEquiv (fun field => (data field).cap + 1)).symm)

def leafBids {m : ℕ} (data : Fin m → ProposalLeaf) (field : Fin m) (code : Fin ((data field).cap + 1)) : ℚ :=
  (data field).decode code.val

def leafWeights {m : ℕ} (data : Fin m → ProposalLeaf) (field : Fin m) (code : Fin ((data field).cap + 1)) : ℚ :=
  labelMass (data field).blocks code.val

theorem leafWeights_positive {m : ℕ} (data : Fin m → ProposalLeaf) : ∀ field code, 0 < leafWeights data field code :=
  fun field code => partition_labelMass_positive (data field).cap (data field).blocks (data field).partition (data field).positive code

theorem leafComb_allocation_eq_raw (n : ℕ) (data : Fin (n + 1) → ProposalLeaf)
    (hn : ∀ field (code : Fin ((data field).cap + 1)), 0 ≤ (data field).decode code.val) :
    (leafComb n data).allocationTree (leafComb_nonnegative n data hn) =
      ProductArrayTree.raw n (fun field => (data field).cap + 1) (leafBids data) (leafWeights data)
        hn (fun field code => (leafWeights_positive data field code).le) := by
  induction n with
  | zero =>
    congr 1

  | succ n ih =>
    change ProductBidTree.fork _ _ (.leaf (data 0).family _ _ _) ((leafComb n _).allocationTree _) = _
    rw [ih (fun field => data field.succ) (fun field => hn field.succ)]
    congr 1

theorem raw_target_prefix (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (field : Fin (n + 1)) → Fin (sizes field) → ℚ)
    (hb : ∀ field code, 0 ≤ bids field code) (hw : ∀ field code, 0 ≤ weights field code) (budget : ℚ) :
    (ProductArrayTree.raw n sizes bids weights hb hw).guideTree.real.trueFamily.prefixMass (budget : ℝ) =
      ((∑ index, SparseMW.feasibleVector bids budget weights index : ℚ) : ℝ) := by
  let tree := ProductArrayTree.raw n sizes bids weights hb hw
  unfold WeightedResourceFamily.prefixMass
  rw [← Equiv.sum_comp (ProductArrayTree.finCastEquiv (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm)]
  have hNative : (∑ label : Fin tree.labels, if tree.guideTree.real.trueFamily.resource
      (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm) ≤ (budget : ℝ) then
      tree.guideTree.real.trueFamily.mass (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm) else 0) =
      ∑ label : Fin tree.labels, if tree.resource label ≤ budget then (tree.weight label : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro label _
    rw [← tree.resource_eq_trueFamily label, ← tree.weight_eq_trueFamily label]
    have hc : (tree.resource label : ℝ) ≤ (budget : ℝ) ↔ tree.resource label ≤ budget := by norm_cast
    simp only [hc]
  change (∑ label : Fin tree.labels, if tree.guideTree.real.trueFamily.resource
      (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm) ≤ (budget : ℝ) then
      tree.guideTree.real.trueFamily.mass (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm) else 0) = _
  rw [hNative]
  have hCode : (∑ label : Fin tree.labels, if tree.resource label ≤ budget then tree.weight label else 0) =
      ∑ code : SparseMW.ProductCodes sizes, if SparseMW.productResource bids code ≤ budget then SparseMW.productMass weights code else 0 := by
    apply Fintype.sum_equiv (ProductArrayTree.labelEquiv n sizes bids weights hb hw)
    intro label
    rw [ProductArrayTree.raw_resource, ProductArrayTree.raw_weight]
  have hSum : (∑ label : Fin tree.labels, if tree.resource label ≤ budget then tree.weight label else 0) =
      ∑ index, SparseMW.feasibleVector bids budget weights index := by
    rw [hCode, ProductArrayTree.sum_ite_subtype]
    have he := Equiv.sum_comp (SparseMW.feasibleEquiv bids budget) (SparseMW.feasibleVector bids budget weights)
    simp only [SparseMW.feasibleVector, SparseMW.feasibleMass, Equiv.symm_apply_apply] at he
    exact he
  have hCast : (∑ label : Fin tree.labels, if tree.resource label ≤ budget then (tree.weight label : ℝ) else 0) =
      ((∑ label : Fin tree.labels, if tree.resource label ≤ budget then tree.weight label else 0 : ℚ) : ℝ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro label _
    split_ifs <;> simp
  rw [hCast, hSum]

theorem raw_target_mean (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (field : Fin (n + 1)) → Fin (sizes field) → ℚ)
    (hb : ∀ field code, 0 ≤ bids field code) (hw : ∀ field code, 0 < weights field code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (_hf : SparseMW.productResource bids fallback ≤ budget)
    (hm : 0 < (ProductArrayTree.raw n sizes bids weights hb (fun field code => (hw field code).le)).guideTree.real.trueFamily.prefixMass (budget : ℝ))
    (test : SparseMW.ProductCodes sizes → ℝ) :
    let tree := ProductArrayTree.raw n sizes bids weights hb (fun field code => (hw field code).le)
    (tree.guideTree.targetKernel budget hm).mean (fun label => test (ProductArrayTree.labelEquiv n sizes bids weights hb _
      (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize)))) =
      ∑ index, (SparseMW.normalizeQ (SparseMW.feasibleVector bids budget weights) index : ℝ) *
        test (((SparseMW.feasibleEquiv bids budget).symm index).val) := by
  dsimp only
  let tree := ProductArrayTree.raw n sizes bids weights hb (fun field code => (hw field code).le)
  let denom : ℝ := ((∑ index, SparseMW.feasibleVector bids budget weights index : ℚ) : ℝ)
  change (∑ label : Fin tree.guideTree.real.trueSize, tree.guideTree.real.feasibleTargetWeight (budget : ℝ) label /
    tree.guideTree.real.trueFamily.prefixMass (budget : ℝ) *
      test (ProductArrayTree.labelEquiv n sizes bids weights hb _ (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize)))) = _
  rw [raw_target_prefix]
  rw [← Equiv.sum_comp (ProductArrayTree.finCastEquiv (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm)]
  have hNative : (∑ label : Fin tree.labels,
      tree.guideTree.real.feasibleTargetWeight (budget : ℝ)
        (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm) / denom *
        test (ProductArrayTree.labelEquiv n sizes bids weights hb _ label)) =
      ∑ label : Fin tree.labels, if tree.resource label ≤ budget then (tree.weight label : ℝ) / denom *
        test (ProductArrayTree.labelEquiv n sizes bids weights hb _ label) else 0 := by
    apply Finset.sum_congr rfl
    intro label _
    unfold WeightedGuideTree.feasibleTargetWeight
    rw [← tree.resource_eq_trueFamily label, ← tree.weight_eq_trueFamily label]
    have hc : (tree.resource label : ℝ) ≤ (budget : ℝ) ↔ tree.resource label ≤ budget := by norm_cast
    simp only [hc]
    split_ifs <;> simp
  change (∑ label : Fin tree.labels, _) = _
  have hCasts : ∀ label : Fin tree.labels,
      (ProductArrayTree.finCastEquiv (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm label).cast
        (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize) = label := fun _ => Fin.ext rfl
  simp_rw [hCasts]
  change (∑ label : Fin tree.labels, tree.guideTree.real.feasibleTargetWeight (budget : ℝ)
    (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize).symm) / denom *
      test (ProductArrayTree.labelEquiv n sizes bids weights hb _ label)) = _
  rw [hNative]
  rw [← Equiv.sum_comp (ProductArrayTree.labelEquiv n sizes bids weights hb (fun field code => (hw field code).le)).symm]
  dsimp only [tree]
  simp_rw [ProductArrayTree.raw_resource, ProductArrayTree.raw_weight]
  simp only [Equiv.apply_symm_apply]
  rw [ProductArrayTree.sum_ite_subtype_real]
  have he := Equiv.sum_comp (SparseMW.feasibleEquiv bids budget)
    (fun index => (SparseMW.normalizeQ (SparseMW.feasibleVector bids budget weights) index : ℝ) *
      test (((SparseMW.feasibleEquiv bids budget).symm index).val))
  simp only [SparseMW.normalizeQ, SparseMW.feasibleVector, SparseMW.feasibleMass, Equiv.symm_apply_apply, Rat.cast_div, Rat.cast_sum] at he
  simpa only [denom, SparseMW.normalizeQ, SparseMW.feasibleVector, SparseMW.feasibleMass, Rat.cast_div, Rat.cast_sum] using he

theorem raw_target_row_mean (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (field : Fin (n + 1)) → Fin (sizes field) → ℚ)
    (hb : ∀ field code, 0 ≤ bids field code) (hw : ∀ field code, 0 < weights field code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget)
    (hm : 0 < (ProductArrayTree.raw n sizes bids weights hb (fun field code => (hw field code).le)).guideTree.real.trueFamily.prefixMass (budget : ℝ))
    (test : (Fin (n + 1) → ℚ) → ℝ) :
    let tree := ProductArrayTree.raw n sizes bids weights hb (fun field code => (hw field code).le)
    (tree.guideTree.targetKernel budget hm).mean (fun label => test (fun field =>
      tree.decode (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize))
        (field.cast (ProductArrayTree.raw_fields n sizes bids weights hb _).symm))) =
      ∑ index, (SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).realWeight index *
        test ((SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).row index) := by
  dsimp only
  have he := raw_target_mean n sizes bids weights hb hw budget fallback hf hm
    (fun code => test (fun field => bids field (code field)))
  let tree := ProductArrayTree.raw n sizes bids weights hb (fun field code => (hw field code).le)
  have hRow : ∀ label : Fin tree.guideTree.real.trueSize,
      (fun field => tree.decode (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize))
        (field.cast (ProductArrayTree.raw_fields n sizes bids weights hb (fun field code => (hw field code).le)).symm)) =
      (fun field => bids field (ProductArrayTree.labelEquiv n sizes bids weights hb (fun field code => (hw field code).le)
        (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize)) field)) := by
    intro label
    funext field
    exact ProductArrayTree.raw_decode n sizes bids weights hb (fun field code => (hw field code).le)
      (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize)) field
  change (tree.guideTree.targetKernel budget hm).mean (fun label => test (fun field => tree.decode
    (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize))
      (field.cast (ProductArrayTree.raw_fields n sizes bids weights hb (fun field code => (hw field code).le)).symm))) = _
  simp_rw [hRow]
  exact he

theorem tree_target_transport {fields : ℕ} (first last : ProductBidTree) (he : first = last)
    (hFieldsFirst : first.fields = fields) (hFieldsLast : last.fields = fields) (budget : ℚ)
    (hmFirst : 0 < first.guideTree.real.trueFamily.prefixMass (budget : ℝ))
    (hmLast : 0 < last.guideTree.real.trueFamily.prefixMass (budget : ℝ)) (test : (Fin fields → ℚ) → ℝ) :
    (first.guideTree.targetKernel budget hmFirst).mean (fun label => test (fun field => first.decode
      (label.cast (first.guideTree.real_trueSize.trans first.guideTree_trueSize)) (field.cast hFieldsFirst.symm))) =
    (last.guideTree.targetKernel budget hmLast).mean (fun label => test (fun field => last.decode
      (label.cast (last.guideTree.real_trueSize.trans last.guideTree_trueSize)) (field.cast hFieldsLast.symm))) := by
  subst last
  rfl

theorem leafComb_target_rational_mean (n : ℕ) (data : Fin (n + 1) → ProposalLeaf)
    (hn : ∀ field (code : Fin ((data field).cap + 1)), 0 ≤ (data field).decode code.val)
    (budget : ℚ) (fallback : SparseMW.ProductCodes (fun field => (data field).cap + 1))
    (hf : SparseMW.productResource (leafBids data) fallback ≤ budget)
    (hm : 0 < (leafComb n data).projected.real.trueFamily.prefixMass (budget : ℝ))
    (test : (Fin (n + 1) → ℚ) → ℝ) :
    ((leafComb n data).projected.targetKernel budget hm).mean (fun label =>
      test (fun field => (leafComb n data).decodeLabel (leafComb_nonnegative n data hn)
        (label.cast (leafComb n data).projected.real_trueSize) (field.cast (leafComb_fields n data hn).symm))) =
      ∑ index, (SparseMW.gibbsWholeRowLaw (leafBids data) budget fallback hf (leafWeights data) (leafWeights_positive data)).realWeight index *
        test ((SparseMW.gibbsWholeRowLaw (leafBids data) budget fallback hf (leafWeights data) (leafWeights_positive data)).row index) := by
  let view := (leafComb n data).allocationTree (leafComb_nonnegative n data hn)
  have hTree := (leafComb n data).allocationTree_projected (leafComb_nonnegative n data hn)
  have hView := leafComb_allocation_eq_raw n data hn
  have hmView : 0 < view.guideTree.real.trueFamily.prefixMass (budget : ℝ) := by rw [hTree]; exact hm
  have hmRaw : 0 < (ProductArrayTree.raw n (fun field => (data field).cap + 1) (leafBids data) (leafWeights data)
      hn (fun field code => (leafWeights_positive data field code).le)).guideTree.real.trueFamily.prefixMass (budget : ℝ) := by
    rw [← hView]
    exact hmView
  have hTransport := tree_target_transport view _ hView (leafComb_fields n data hn)
    (ProductArrayTree.raw_fields n _ _ _ hn _) budget hmView hmRaw test
  have hMean := raw_target_row_mean n (fun field => (data field).cap + 1) (leafBids data) (leafWeights data)
    hn (leafWeights_positive data) budget fallback hf hmRaw test
  have hProjection : ((leafComb n data).projected.targetKernel budget hm).mean (fun label =>
      test (fun field => (leafComb n data).decodeLabel (leafComb_nonnegative n data hn)
        (label.cast (leafComb n data).projected.real_trueSize) (field.cast (leafComb_fields n data hn).symm))) =
      (view.guideTree.targetKernel budget hmView).mean (fun label => test (fun field => view.decode
        (label.cast (view.guideTree.real_trueSize.trans view.guideTree_trueSize)) (field.cast (leafComb_fields n data hn).symm))) := by
    have hGeneral : ∀ (first : RationalWeightedGuideTree) (allocation : ProductBidTree) (he : allocation.guideTree = first)
        (hFields : allocation.fields = n + 1) (hmF : 0 < first.real.trueFamily.prefixMass (budget : ℝ))
        (hmA : 0 < allocation.guideTree.real.trueFamily.prefixMass (budget : ℝ)),
        (first.targetKernel budget hmF).mean (fun label => test (fun field => allocation.decode
          ((label.cast first.real_trueSize).cast (allocation.guideTree_trueSize.symm.trans (congrArg RationalWeightedGuideTree.trueSize he)).symm)
          (field.cast hFields.symm))) =
        (allocation.guideTree.targetKernel budget hmA).mean (fun label => test (fun field => allocation.decode
          (label.cast (allocation.guideTree.real_trueSize.trans allocation.guideTree_trueSize)) (field.cast hFields.symm))) := by
      intro first allocation he hFields hmF hmA
      subst first
      rfl
    exact hGeneral _ _ hTree (leafComb_fields n data hn) hm hmView
  exact hProjection.trans (hTransport.trans hMean)

theorem roundedTree_target_rational_mean {a : ℕ} (n : ℕ) (caps : Fin (n + 1) → ℕ)
    (decode : Fin (n + 1) → ℕ → ℚ)
    (hmDecode : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (hn : ∀ field code, code ≤ caps field → 0 ≤ decode field code)
    (selected : List (Fin a) → Fin a → Fin (n + 1)) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (budget : ℚ)
    (fallback : SparseMW.ProductCodes (fun field => caps field + 1))
    (hf : SparseMW.productResource (fun field code => decode field code.val) fallback ≤ budget)
    (hm : 0 < (roundedTree n caps decode hmDecode selected opponent eta theta heta htheta past).projected.real.trueFamily.prefixMass (budget : ℝ))
    (test : (Fin (n + 1) → ℚ) → ℝ) :
    let data := roundedProposalLeaf caps decode hmDecode selected opponent eta theta heta htheta past
    let hNonnegative := fun field (code : Fin (caps field + 1)) => hn field code.val (show code.val ≤ caps field from by omega)
    let tree := roundedTree n caps decode hmDecode selected opponent eta theta heta htheta past
    (tree.projected.targetKernel budget hm).mean (fun label => test (fun field =>
      tree.decodeLabel (leafComb_nonnegative n data hNonnegative) (label.cast tree.projected.real_trueSize)
        (field.cast (leafComb_fields n data hNonnegative).symm))) =
      ∑ index, (SparseMW.gibbsWholeRowLaw (fun field code => decode field code.val) budget fallback hf
        (SparseMW.roundedFieldHistory (sizes := fun field => caps field + 1) selected
          (resourceLoss caps decode selected opponent) eta theta past)
        (SparseMW.roundedFieldHistory_positive (sizes := fun field => caps field + 1) selected (resourceLoss caps decode selected opponent) eta theta heta htheta
          (resourceLoss_unit caps decode selected opponent) past)).realWeight index *
        test ((SparseMW.gibbsWholeRowLaw (fun field code => decode field code.val) budget fallback hf
          (SparseMW.roundedFieldHistory (sizes := fun field => caps field + 1) selected
            (resourceLoss caps decode selected opponent) eta theta past)
          (SparseMW.roundedFieldHistory_positive (sizes := fun field => caps field + 1) selected (resourceLoss caps decode selected opponent) eta theta heta htheta
            (resourceLoss_unit caps decode selected opponent) past)).row index) := by
  dsimp only
  let data := roundedProposalLeaf caps decode hmDecode selected opponent eta theta heta htheta past
  let hNonnegative := fun field (code : Fin (caps field + 1)) => hn field code.val (show code.val ≤ caps field from by omega)
  have hWeights : leafWeights data = SparseMW.roundedFieldHistory (sizes := fun field => caps field + 1)
      selected (resourceLoss caps decode selected opponent) eta theta past := by
    funext field code
    exact roundedProposalLeaf_mass caps decode hmDecode selected opponent eta theta heta htheta past field code
  have he := leafComb_target_rational_mean n data hNonnegative budget fallback hf hm test
  unfold SparseMW.gibbsWholeRowLaw RationalWholeRowLaw.realWeight at he ⊢
  dsimp only at he ⊢
  rw [hWeights] at he
  exact he

theorem leafComb_zero_draw_gibbs_error (n : ℕ) (data : Fin (n + 1) → ProposalLeaf)
    (hn : ∀ field (code : Fin ((data field).cap + 1)), 0 ≤ (data field).decode code.val)
    (hz : ∀ field, (data field).decode 0 = 0) (budget : ℚ) (hb : 0 ≤ budget) (epsilon : ℚ) (he : 0 < epsilon)
    (fallback : SparseMW.ProductCodes (fun field => (data field).cap + 1))
    (hf : SparseMW.productResource (leafBids data) fallback ≤ budget)
    (test : (Fin (n + 1) → ℚ) → ℝ) (hTest : ∀ row, 0 ≤ test row ∧ test row ≤ 1) :
    let tree := leafComb n data
    let hNonnegative := leafComb_nonnegative n data hn
    let hZero := leafComb_zero n data hz
    |(fairBitKernel (tree.constructed.epsilonSeedBudget epsilon)).mean (fun bits => test (fun field =>
      tree.zeroFallbackRow hNonnegative hZero budget hb epsilon bits (field.cast (leafComb_fields n data hn).symm))) -
      ∑ index, (SparseMW.gibbsWholeRowLaw (leafBids data) budget fallback hf (leafWeights data) (leafWeights_positive data)).realWeight index *
        test ((SparseMW.gibbsWholeRowLaw (leafBids data) budget fallback hf (leafWeights data) (leafWeights_positive data)).row index)| ≤ (epsilon : ℝ) := by
  dsimp only
  let tree := leafComb n data
  let hNonnegative := leafComb_nonnegative n data hn
  let hZero := leafComb_zero n data hz
  let testFields := fun row : Allocation (tree.allocationTree hNonnegative).fields =>
    test (fun field => PreparedProductSampler.rationalizeRow row (field.cast (leafComb_fields n data hn).symm))
  have hContract := (tree.zeroFallbackRow_contract hNonnegative hZero budget hb epsilon he).2 testFields (fun row => hTest _)
  have hNative : ∀ bits, testFields (fun field => (tree.zeroFallbackRow hNonnegative hZero budget hb epsilon bits field : ℝ)) =
      test (fun field => tree.zeroFallbackRow hNonnegative hZero budget hb epsilon bits (field.cast (leafComb_fields n data hn).symm)) := by
    intro bits
    unfold testFields
    change test (fun field => PreparedProductSampler.rationalizeRow
      (PreparedProductSampler.castRow (tree.zeroFallbackRow hNonnegative hZero budget hb epsilon bits))
      (field.cast (leafComb_fields n data hn).symm)) = _
    rw [PreparedProductSampler.rationalizeRow_cast]
  have hTarget : (tree.projected.targetKernel budget (tree.prefix_positive_of_feasible_label budget tree.zeroLabel
      (tree.zeroLabel_feasible hZero budget hb))).mean (fun label => testFields (tree.targetAllocation hNonnegative label)) =
      ∑ index, (SparseMW.gibbsWholeRowLaw (leafBids data) budget fallback hf (leafWeights data) (leafWeights_positive data)).realWeight index *
        test ((SparseMW.gibbsWholeRowLaw (leafBids data) budget fallback hf (leafWeights data) (leafWeights_positive data)).row index) := by
    have he := leafComb_target_rational_mean n data hn budget fallback hf
      (tree.prefix_positive_of_feasible_label budget tree.zeroLabel (tree.zeroLabel_feasible hZero budget hb)) test
    change (tree.projected.targetKernel budget _).mean (fun label => test
      (fun field => PreparedProductSampler.rationalizeRow
        (PreparedProductSampler.castRow (tree.decodeLabel hNonnegative (label.cast tree.projected.real_trueSize)))
        (field.cast (leafComb_fields n data hn).symm))) = _
    simp_rw [PreparedProductSampler.rationalizeRow_cast]
    exact he
  simp_rw [hNative] at hContract
  rw [hTarget] at hContract
  exact hContract

end ImplicitLeafCounts
end Blotto
