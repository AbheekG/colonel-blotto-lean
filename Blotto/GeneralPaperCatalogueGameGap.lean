import Blotto.GeneralPaperCatalogueMixtureOptimizer

/-! The averaged four-regret distance inequality and finite game gap for
the actual own-tree source. Comparator laws consist of feasible complete
literal code rows and may have real weights. All regret, error, optimizer,
incoming-tree and chosen-row dependencies are discharged by execution.
-/
namespace Blotto.GeneralPaperCatalogueGameGap
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCodeCDF GeneralPaperCatalogueFiniteFamilies
open GeneralPaperFourAverageAlgebra GeneralPaperFourAverageGap
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def trajectory {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Trajectory m (2^a.lambda) :=
  ⟨unsigned false a k Qv weights Bc Br,unsigned true a k Qv weights Bc Br,
    signedFamily false a k Qv weights Bc Br,signedFamily true a k Qv weights Bc Br,
    row false a k Qv weights Bc Br,row true a k Qv weights Bc Br⟩

theorem regret_pairings {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (x y : Fin m → Fin (2^a.lambda) → ℝ) (testLambda testMu : Fin m → Fin (2^a.lambda+2^a.lambda) → ℝ) :
    regretMean (trajectory a k Qv weights Bc Br) (GeneralPaperCatalogueGlobalRegret.values Qv weights)
      (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows x y testLambda testMu=
      (∑ time ∈ Finset.range (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows,
        ∑ j, GeneralPaperCatalogueGlobalRegret.values Qv weights j*
          GeneralPaperCatalogueFourPairings.pairings a k Qv weights Bc Br time j (x j) (y j) (testLambda j) (testMu j))/
          (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows := by
  unfold regretMean
  congr 1
  apply Finset.sum_congr rfl
  intro time ht
  apply Finset.sum_congr rfl
  intro j hj
  rw [GeneralPaperCatalogueFourPairings.pairings_eq a k Qv weights Bc Br time (Finset.mem_range.mp ht) j]
  rfl

theorem regret_bound {m : ℕ} (a : Alphabet) (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ)
    (x y : Fin m → Fin (2^a.lambda) → ℝ) (hx : ∀ j, Probability (x j)) (hy : ∀ j, Probability (y j))
    (testLambda testMu : Fin m → Fin (2^a.lambda+2^a.lambda) → ℝ)
    (hl : ∀ j, Probability (testLambda j)) (hm : ∀ j, Probability (testMu j)) :
    regretMean (trajectory a k Qv weights Bc Br) (GeneralPaperCatalogueGlobalRegret.values Qv weights)
      (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows x y testLambda testMu+
      2*(25*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/16)<((GeneralPaperSourceParameters.prepare k).z:ℝ)/64 := by
  rw [regret_pairings]
  exact GeneralPaperCataloguePairingRegret.average_bound a k Qv hQv weights hWeights Bc Br x y testLambda testMu hx hy hl hm

theorem four_regret {m : ℕ} (a : Alphabet) (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ)
    (X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false Bc)
    (Y : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a true Br) :
    let tr := trajectory a k Qv weights Bc Br
    let T := (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows
    let v := GeneralPaperCatalogueGlobalRegret.values Qv weights
    weightedPayoff v (meanP tr T) (GeneralPaperCodeMixture.marginal Y.law)-
      weightedPayoff v (GeneralPaperCodeMixture.marginal X.law) (meanQ tr T)+
      weightedDistance (Nat.two_pow_pos a.lambda) v (meanP tr T) (meanX tr T)+
      weightedDistance (Nat.two_pow_pos a.lambda) v (meanQ tr T) (meanY tr T)<((GeneralPaperSourceParameters.prepare k).z:ℝ)/64 := by
  dsimp only
  apply GeneralPaperFourAverageGap.four_regret (Nat.two_pow_pos a.lambda) _ _ _
    (GeneralPaperTrajectoryParameters.rows_positive a.lambda k) _ _
    (fun j => (GeneralPaperCodeMixture.marginal_probability Y.law j).2)
    (fun t _ j => (unsigned_probability true a k Qv weights Bc Br t j).2)
    (25*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/16) _
  · intro testLambda testMu hl hm
    exact regret_bound a k Qv hQv weights hWeights Bc Br _ _
      (GeneralPaperCodeMixture.marginal_probability X.law) (GeneralPaperCodeMixture.marginal_probability Y.law) testLambda testMu hl hm
  · intro t ht
    exact GeneralPaperCatalogueMixtureOptimizer.residual_lower false a k Qv hQv weights hWeights Bc Br t ht X
  · intro t ht
    exact GeneralPaperCatalogueMixtureOptimizer.residual_lower true a k Qv hQv weights hWeights Bc Br t ht Y

theorem empirical_gap {m : ℕ} (a : Alphabet) (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ)
    (X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false Bc)
    (Y : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a true Br) :
    let tr := trajectory a k Qv weights Bc Br
    let T := (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows
    let v := GeneralPaperCatalogueGlobalRegret.values Qv weights
    weightedPayoff v (meanX tr T) (GeneralPaperCodeMixture.marginal Y.law)-
      weightedPayoff v (GeneralPaperCodeMixture.marginal X.law) (meanY tr T)<((GeneralPaperSourceParameters.prepare k).z:ℝ)/64 := by
  dsimp only
  apply GeneralPaperFourAverageGap.empirical_gap (Nat.two_pow_pos a.lambda) _ _
    (GeneralPaperCatalogueGlobalRegret.values_nonnegative Qv weights) _
    (GeneralPaperTrajectoryParameters.rows_positive a.lambda k) _ _
    (GeneralPaperCodeMixture.marginal_probability X.law) (GeneralPaperCodeMixture.marginal_probability Y.law)
    (fun t _ j => unsigned_probability true a k Qv weights Bc Br t j)
    (25*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/16) _
  · intro testLambda testMu hl hm
    exact regret_bound a k Qv hQv weights hWeights Bc Br _ _
      (GeneralPaperCodeMixture.marginal_probability X.law) (GeneralPaperCodeMixture.marginal_probability Y.law) testLambda testMu hl hm
  · intro t ht
    exact GeneralPaperCatalogueMixtureOptimizer.residual_lower false a k Qv hQv weights hWeights Bc Br t ht X
  · intro t ht
    exact GeneralPaperCatalogueMixtureOptimizer.residual_lower true a k Qv hQv weights hWeights Bc Br t ht Y

end Blotto.GeneralPaperCatalogueGameGap
