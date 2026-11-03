import Blotto.GeneralPaperCatalogueChosenMixture

/-! The code-payoff of two whole-row mixtures is the independent double
row expectation. Coordinate marginals are linear observers of the joint
row laws, not instructions to resample coordinates independently.
-/
namespace Blotto.GeneralPaperCodeMixturePayoff
open scoped BigOperators
open GeneralPaperCodeCDF GeneralPaperFourLossAlgebra GeneralPaperCodeAverages GeneralPaperCodeMixture GeneralPaperFourAverageGap
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem coordinate_payoff {m n : ℕ} (X Y : Mixture m n) (j : Fin m) :
    codePayoff (GeneralPaperCodeMixture.marginal X j) (GeneralPaperCodeMixture.marginal Y j)=
      ∑ y, Y.weight y*(∑ x, X.weight x*kernel (X.rows x j) (Y.rows y j)) := by
  rw [payoff_response]
  change dot (GeneralPaperCodeMixture.marginal Y j) (half (GeneralPaperCodeMixture.marginal X j))=_
  rw [marginal_dot]
  apply Finset.sum_congr rfl
  intro y hy
  rw [point_dot,half_kernel]
  change Y.weight y*dot (GeneralPaperCodeMixture.marginal X j) (fun a => kernel a (Y.rows y j))=_
  rw [marginal_dot]
  simp only [point_dot]

theorem weighted_payoff {m n : ℕ} (v : Fin m → ℝ) (X Y : Mixture m n) :
    weightedPayoff v (GeneralPaperCodeMixture.marginal X) (GeneralPaperCodeMixture.marginal Y)=
      ∑ y, Y.weight y*(∑ x, X.weight x*(∑ j, v j*kernel (X.rows x j) (Y.rows y j))) := by
  unfold weightedPayoff
  simp only [coordinate_payoff,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Blotto.GeneralPaperCodeMixturePayoff
