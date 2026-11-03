import Blotto.RoundedImplicitGibbsLaw
import Blotto.SizedImplicitSampler

/-! Prepared succinct leaf trees draw whole rational rows from stored guides.
Their exact target is the original constrained Gibbs law. Size equalities only
reindex coordinates; no native Cartesian array is constructed. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts

def prepareLeafComb (n : ℕ) (data : Fin (n + 1) → ProposalLeaf)
    (hn : ∀ field (code : Fin ((data field).cap + 1)), 0 ≤ (data field).decode code.val)
    (hz : ∀ field, (data field).decode 0 = 0) (budget : ℚ) (hb : 0 ≤ budget) : SizedImplicitSampler (n + 1) where
  stored := (leafComb n data).prepareZero (leafComb_nonnegative n data hn) (leafComb_zero n data hz) budget hb
  fields := ((leafComb n data).rebuild_allocation_fields (leafComb_nonnegative n data hn)
    (leafComb n data).constructionGamma (leafComb n data).constructionGamma_ge_one).trans (leafComb_fields n data hn)

theorem prepareLeafComb_budget (n : ℕ) (data : Fin (n + 1) → ProposalLeaf)
    (hn : ∀ field (code : Fin ((data field).cap + 1)), 0 ≤ (data field).decode code.val)
    (hz : ∀ field, (data field).decode 0 = 0) (budget : ℚ) (hb : 0 ≤ budget) :
    (prepareLeafComb n data hn hz budget hb).budget = budget := rfl

theorem rebuilt_decodeLabel (tree : ProposalTree) (hn : tree.NonnegativeResources)
    (label : Fin tree.constructed.projected.trueSize) (field : Fin (tree.allocationTree hn).fields) :
    tree.constructed.decodeLabel (tree.rebuild_nonnegativeResources hn _ _) label
      (field.cast (tree.rebuild_allocation_fields hn _ _).symm) =
    tree.decodeLabel hn (label.cast tree.constructed_trueSize) field := by
  have he := tree.rebuild_allocation_decode hn tree.constructionGamma tree.constructionGamma_ge_one
    ((label.cast tree.constructed_trueSize).cast (tree.allocationTree_labels hn).symm) field
  have hi : (((label.cast tree.constructed_trueSize).cast (tree.allocationTree_labels hn).symm).cast
      (tree.rebuild_allocation_labels hn _ _).symm) =
      label.cast (tree.constructed.allocationTree_labels (tree.rebuild_nonnegativeResources hn _ _)).symm := Fin.ext rfl
  rw [hi] at he
  exact he

theorem prepareLeafComb_target_mean (n : ℕ) (data : Fin (n + 1) → ProposalLeaf)
    (hn : ∀ field (code : Fin ((data field).cap + 1)), 0 ≤ (data field).decode code.val)
    (hz : ∀ field, (data field).decode 0 = 0) (budget : ℚ) (hb : 0 ≤ budget)
    (fallback : SparseMW.ProductCodes (fun field => (data field).cap + 1))
    (hf : SparseMW.productResource (leafBids data) fallback ≤ budget)
    (test : (Fin (n + 1) → ℚ) → ℝ) :
    (prepareLeafComb n data hn hz budget hb).targetKernel.mean test =
      ∑ index, (SparseMW.gibbsWholeRowLaw (leafBids data) budget fallback hf (leafWeights data) (leafWeights_positive data)).realWeight index *
        test ((SparseMW.gibbsWholeRowLaw (leafBids data) budget fallback hf (leafWeights data) (leafWeights_positive data)).row index) := by
  let tree := leafComb n data
  let hNonnegative := leafComb_nonnegative n data hn
  let hZero := leafComb_zero n data hz
  have hOriginal := tree.prefix_positive_of_feasible_label budget tree.zeroLabel (tree.zeroLabel_feasible hZero budget hb)
  have hRows : ∀ label : Fin tree.constructed.projected.real.trueSize,
      test ((prepareLeafComb n data hn hz budget hb).reindex
        (tree.constructed.decodeLabel (tree.rebuild_nonnegativeResources hNonnegative _ _)
          (label.cast tree.constructed.projected.real_trueSize))) =
      test (fun field => tree.decodeLabel hNonnegative
        ((label.cast tree.constructed_real_trueSize).cast tree.projected.real_trueSize)
          (field.cast (leafComb_fields n data hn).symm)) := by
    intro label
    apply congrArg test
    funext field
    have he := rebuilt_decodeLabel tree hNonnegative (label.cast tree.constructed.projected.real_trueSize)
      (field.cast (leafComb_fields n data hn).symm)
    exact he
  change (tree.constructed.projected.targetKernel budget
    (tree.constructed_prefix_positive budget tree.zeroLabel (tree.zeroLabel_feasible hZero budget hb))).mean (fun label => test
    ((prepareLeafComb n data hn hz budget hb).reindex
      (tree.constructed.decodeLabel (tree.rebuild_nonnegativeResources hNonnegative _ _)
        (label.cast tree.constructed.projected.real_trueSize)))) = _
  simp_rw [hRows]
  have hMean := tree.constructed_target_mean budget hOriginal
    (fun label => test (fun field => tree.decodeLabel hNonnegative (label.cast tree.projected.real_trueSize)
      (field.cast (leafComb_fields n data hn).symm)))
  exact hMean.trans (leafComb_target_rational_mean n data hn budget fallback hf hOriginal test)

theorem prepareLeafComb_sample_gibbs_error (n : ℕ) (data : Fin (n + 1) → ProposalLeaf)
    (hn : ∀ field (code : Fin ((data field).cap + 1)), 0 ≤ (data field).decode code.val)
    (hz : ∀ field, (data field).decode 0 = 0) (budget : ℚ) (hb : 0 ≤ budget)
    (fallback : SparseMW.ProductCodes (fun field => (data field).cap + 1))
    (hf : SparseMW.productResource (leafBids data) fallback ≤ budget) (epsilon : ℚ) (he : 0 < epsilon)
    (test : (Fin (n + 1) → ℚ) → ℝ) (hTest : ∀ row, 0 ≤ test row ∧ test row ≤ 1) :
    |(fairBitKernel ((prepareLeafComb n data hn hz budget hb).bitBudget epsilon)).mean
      (fun bits => test ((prepareLeafComb n data hn hz budget hb).sample epsilon bits)) -
      ∑ index, (SparseMW.gibbsWholeRowLaw (leafBids data) budget fallback hf (leafWeights data) (leafWeights_positive data)).realWeight index *
        test ((SparseMW.gibbsWholeRowLaw (leafBids data) budget fallback hf (leafWeights data) (leafWeights_positive data)).row index)| ≤ (epsilon : ℝ) := by
  have h := (prepareLeafComb n data hn hz budget hb).nativeKernel_close epsilon he test hTest
  rw [prepareLeafComb_target_mean n data hn hz budget hb fallback hf test] at h
  exact h

def prepareRounded {a : ℕ} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (hn : ∀ field code, code ≤ caps field → 0 ≤ decode field code) (hz : ∀ field, decode field 0 = 0)
    (selected : List (Fin a) → Fin a → Fin (n + 1)) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (budget : ℚ) (hb : 0 ≤ budget) : SizedImplicitSampler (n + 1) :=
  prepareLeafComb n (roundedProposalLeaf caps decode hm selected opponent eta theta heta htheta past)
    (fun field code => hn field code.val (by have hc := code.isLt; change code.val < caps field + 1 at hc; omega)) hz budget hb

theorem prepareRounded_budget {a : ℕ} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (hn : ∀ field code, code ≤ caps field → 0 ≤ decode field code) (hz : ∀ field, decode field 0 = 0)
    (selected : List (Fin a) → Fin a → Fin (n + 1)) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (budget : ℚ) (hb : 0 ≤ budget) :
    (prepareRounded n caps decode hm hn hz selected opponent eta theta heta htheta past budget hb).budget = budget := rfl

theorem prepareRounded_target_mean {a : ℕ} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (hn : ∀ field code, code ≤ caps field → 0 ≤ decode field code) (hz : ∀ field, decode field 0 = 0)
    (selected : List (Fin a) → Fin a → Fin (n + 1)) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (budget : ℚ) (hb : 0 ≤ budget)
    (fallback : SparseMW.ProductCodes (fun field => caps field + 1))
    (hf : SparseMW.productResource (fun field code => decode field code.val) fallback ≤ budget)
    (test : (Fin (n + 1) → ℚ) → ℝ) :
    (prepareRounded n caps decode hm hn hz selected opponent eta theta heta htheta past budget hb).targetKernel.mean test =
      ∑ index, (SparseMW.gibbsWholeRowLaw (fun field code => decode field code.val) budget fallback hf
        (SparseMW.roundedFieldHistory (sizes := fun field => caps field + 1) selected (resourceLoss caps decode selected opponent) eta theta past)
        (SparseMW.roundedFieldHistory_positive (sizes := fun field => caps field + 1) selected
          (resourceLoss caps decode selected opponent) eta theta heta htheta (resourceLoss_unit caps decode selected opponent) past)).realWeight index *
        test ((SparseMW.gibbsWholeRowLaw (fun field code => decode field code.val) budget fallback hf
          (SparseMW.roundedFieldHistory (sizes := fun field => caps field + 1) selected (resourceLoss caps decode selected opponent) eta theta past)
          (SparseMW.roundedFieldHistory_positive (sizes := fun field => caps field + 1) selected
            (resourceLoss caps decode selected opponent) eta theta heta htheta (resourceLoss_unit caps decode selected opponent) past)).row index) := by
  let data := roundedProposalLeaf caps decode hm selected opponent eta theta heta htheta past
  let hNonnegative := fun field (code : Fin (caps field + 1)) => hn field code.val (show code.val ≤ caps field from by omega)
  have he := prepareLeafComb_target_mean n data hNonnegative hz budget hb fallback hf test
  have hWeights : leafWeights data = SparseMW.roundedFieldHistory (sizes := fun field => caps field + 1) selected
      (resourceLoss caps decode selected opponent) eta theta past := by
    funext field code
    exact roundedProposalLeaf_mass caps decode hm selected opponent eta theta heta htheta past field code
  unfold SparseMW.gibbsWholeRowLaw RationalWholeRowLaw.realWeight at he ⊢
  dsimp only at he ⊢
  rw [hWeights] at he
  exact he

theorem prepareRounded_sample_gibbs_error {a : ℕ} (n : ℕ) (caps : Fin (n + 1) → ℕ) (decode : Fin (n + 1) → ℕ → ℚ)
    (hm : ∀ field, MonotoneResourceCuts.MonotoneDecode (caps field) (decode field))
    (hn : ∀ field code, code ≤ caps field → 0 ≤ decode field code) (hz : ∀ field, decode field 0 = 0)
    (selected : List (Fin a) → Fin a → Fin (n + 1)) (opponent : List (Fin a) → Fin a → ℚ)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1 / 4) (htheta : 0 < theta ∧ theta ≤ 1 / 2)
    (past : List (Fin a)) (budget : ℚ) (hb : 0 ≤ budget)
    (fallback : SparseMW.ProductCodes (fun field => caps field + 1))
    (hf : SparseMW.productResource (fun field code => decode field code.val) fallback ≤ budget)
    (epsilon : ℚ) (he : 0 < epsilon) (test : (Fin (n + 1) → ℚ) → ℝ)
    (hTest : ∀ row, 0 ≤ test row ∧ test row ≤ 1) :
    let prepared := prepareRounded n caps decode hm hn hz selected opponent eta theta heta htheta past budget hb
    |(fairBitKernel (prepared.bitBudget epsilon)).mean (fun bits => test (prepared.sample epsilon bits)) -
      ∑ index, (SparseMW.gibbsWholeRowLaw (fun field code => decode field code.val) budget fallback hf
        (SparseMW.roundedFieldHistory (sizes := fun field => caps field + 1) selected (resourceLoss caps decode selected opponent) eta theta past)
        (SparseMW.roundedFieldHistory_positive (sizes := fun field => caps field + 1) selected
          (resourceLoss caps decode selected opponent) eta theta heta htheta (resourceLoss_unit caps decode selected opponent) past)).realWeight index *
        test ((SparseMW.gibbsWholeRowLaw (fun field code => decode field code.val) budget fallback hf
          (SparseMW.roundedFieldHistory (sizes := fun field => caps field + 1) selected (resourceLoss caps decode selected opponent) eta theta past)
          (SparseMW.roundedFieldHistory_positive (sizes := fun field => caps field + 1) selected
            (resourceLoss caps decode selected opponent) eta theta heta htheta (resourceLoss_unit caps decode selected opponent) past)).row index)| ≤ (epsilon : ℝ) := by
  have h := (prepareRounded n caps decode hm hn hz selected opponent eta theta heta htheta past budget hb).nativeKernel_close epsilon he test hTest
  rw [prepareRounded_target_mean n caps decode hm hn hz selected opponent eta theta heta htheta past budget hb fallback hf test] at h
  exact h

end ImplicitLeafCounts
end Blotto
