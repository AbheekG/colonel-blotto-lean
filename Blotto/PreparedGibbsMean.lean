import Blotto.PreparedRationalTransition

/-! Prepared ideal kernels evaluate exactly the current feasible Gibbs law.
The raw rational mean identity preserves labelled duplicate codes and supports
native-history/finite-index simulation without a unique-row assumption. -/

namespace Blotto
open scoped BigOperators Classical
namespace ProductArrayTree

theorem prepareSampler_target_mean (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 < weights j code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget)
    (test : Allocation (n + 1) → ℝ) :
    (prepareSampler n sizes bids weights hb hw budget fallback hf).targetKernel.mean test =
      ∑ i, (SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).realWeight i *
        test ((SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).realRow i) :=
  constructed_target_row_mean n sizes bids weights hb hw budget fallback hf test

theorem prepareSampler_rational_target_mean (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 < weights j code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget)
    (test : (Fin (n + 1) → ℚ) → ℝ) :
    (prepareSampler n sizes bids weights hb hw budget fallback hf).rationalTargetKernel.mean test =
      ∑ i, (SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).realWeight i *
        test ((SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).row i) := by
  let hn := fun j code => (hw j code).le
  let tree := constructed n sizes bids weights hb hn
  have he := constructed_target_mean n sizes bids weights hb hw budget fallback hf
    (fun code => test (fun field => bids field (code field)))
  have hrows : ∀ label : Fin tree.guideTree.real.trueSize,
      (prepareSampler n sizes bids weights hb hw budget fallback hf).rationalTargetRow label =
        fun field => bids field (constructedLabelEquiv n sizes bids weights hb hn
          (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize)) field) := by
    intro label
    funext field
    exact constructed_decode n sizes bids weights hb hn
      (label.cast (tree.guideTree.real_trueSize.trans tree.guideTree_trueSize)) field
  change (tree.guideTree.targetKernel budget (constructed_prefix_positive n sizes bids weights hb hw budget fallback hf)).mean
    (fun label => test ((prepareSampler n sizes bids weights hb hw budget fallback hf).rationalTargetRow label)) = _
  simp_rw [hrows]
  exact he

theorem prepareSampler_opposing_mean (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (bids weights : (j : Fin (n + 1)) → Fin (sizes j) → ℚ)
    (hb : ∀ j code, 0 ≤ bids j code) (hw : ∀ j code, 0 < weights j code) (budget : ℚ)
    (fallback : SparseMW.ProductCodes sizes) (hf : SparseMW.productResource bids fallback ≤ budget)
    (values : Values (n + 1)) (candidate : Allocation (n + 1)) :
    (prepareSampler n sizes bids weights hb hw budget fallback hf).targetKernel.mean
      (fun row => payoff values row candidate) =
      1 - purePayoff values candidate (SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw).law := by
  rw [prepareSampler_target_mean, RationalWholeRowLaw.purePayoff_eq_sum]
  let law := SparseMW.gibbsWholeRowLaw bids budget fallback hf weights hw
  have hp : ∀ i, payoff values (law.realRow i) candidate = 1 - payoff values candidate (law.realRow i) := by
    intro i
    have he := payoff_constant_sum values (law.realRow i) candidate
    linarith
  change (∑ i, law.realWeight i * payoff values (law.realRow i) candidate) =
    1 - ∑ i, law.realWeight i * payoff values candidate (law.realRow i)
  simp_rw [hp]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, law.realWeight_sum]

end ProductArrayTree
end Blotto
