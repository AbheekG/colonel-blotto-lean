import Blotto.GeneralPaperCodeMixturePhysical

/-! Canonical independent-player payoff gap of the actual uniform whole
candidate/response trajectories. The finite game bound is joined to the
decoded allocations and the computed positive normalized value row.
Continuous-response completeness and the rational comparator remain joins.
-/
namespace Blotto.GeneralPaperCatalogueCanonicalGap
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCatalogueChosenMixture GeneralPaperCodeMixturePhysical
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def normalizedValues {m : ℕ} (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hPositive : ∀ j, 0<weights.read j) (hWeights : ∑ j, weights.read j=Qv) : Values m where
  weight := GeneralPaperCatalogueGlobalRegret.values Qv weights
  positive := fun j => div_pos (by exact_mod_cast hPositive j) (by exact_mod_cast hQv)
  normalized := GeneralPaperCatalogueGlobalRegret.values_sum Qv hQv weights hWeights

noncomputable def strategy {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ)
    (hB : 0≤(if response then Br else Bc)) (qbar : ℕ) : Mixed m :=
  physicalLaw (feasible_empirical response a k Qv hm hQv weights hWeights Bc Br hB) qbar

theorem strategy_supported {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ) (hB : 0≤(if response then Br else Bc))
    (q qbar : ℕ) (hq : 0<q) (hCap : q≤qbar) (hDen : (if response then Br else Bc).den∣q) :
    Supported ((if response then Br else Bc):ℚ) (strategy response a k Qv hm hQv weights hWeights Bc Br hB qbar) :=
  GeneralPaperCodeMixturePhysical.supported a response _ _ q qbar hm hq hCap hDen

theorem canonical_gap {m : ℕ} (a : Alphabet) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hPositive : ∀ j, 0<weights.read j) (hWeights : ∑ j, weights.read j=Qv)
    (Bc Br : ℚ) (hBc : 0≤Bc) (hBr : 0≤Br) (qbar : ℕ) (hQ : 0<qbar)
    (X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false Bc)
    (Y : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a true Br) :
    let v := normalizedValues Qv hQv weights hPositive hWeights
    expected v (physicalLaw Y qbar) (strategy false a k Qv hm hQv weights hWeights Bc Br hBc qbar)-
      expected v (strategy true a k Qv hm hQv weights hWeights Bc Br hBr qbar) (physicalLaw X qbar)<
        ((GeneralPaperSourceParameters.prepare k).z:ℝ)/64 := by
  dsimp only
  unfold strategy
  rw [expected_exact a false true Bc Br _ Y qbar hm hQ,
    expected_exact a false true Bc Br X _ qbar hm hQ]
  have hx : GeneralPaperCodeMixture.marginal (feasible_empirical false a k Qv hm hQv weights hWeights Bc Br hBc).law=
      GeneralPaperFourAverageAlgebra.meanX (GeneralPaperCatalogueGameGap.trajectory a k Qv weights Bc Br)
        (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows :=
    funext (empirical_marginal false a k Qv weights Bc Br)
  have hy : GeneralPaperCodeMixture.marginal (feasible_empirical true a k Qv hm hQv weights hWeights Bc Br hBr).law=
      GeneralPaperFourAverageAlgebra.meanY (GeneralPaperCatalogueGameGap.trajectory a k Qv weights Bc Br)
        (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows :=
    funext (empirical_marginal true a k Qv weights Bc Br)
  rw [hx,hy]
  exact GeneralPaperCatalogueGameGap.empirical_gap a k Qv hQv weights hWeights Bc Br X Y

end Blotto.GeneralPaperCatalogueCanonicalGap
