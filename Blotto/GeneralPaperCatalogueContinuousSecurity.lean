import Blotto.GeneralPaperContinuousResponsePayoff

/-! The actual source's finite-comparator game gap bounds the supremum
over ALL continuous feasible responses. Its actual response trajectory is
feasible, giving comparison with every finite feasible candidate law's
continuous security. The selected near-optimal rational comparator and
paired minimax conclusion remain separate joins.
-/
namespace Blotto.GeneralPaperCatalogueContinuousSecurity
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCatalogueCanonicalGap GeneralPaperCodeMixturePhysical
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem continuous_upper {m : ℕ} (a : Alphabet) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hPositive : ∀ j, 0<weights.read j) (hWeights : ∑ j, weights.read j=Qv)
    (Bc Br : ℚ) (hBc : 0≤Bc) (hBr : 0≤Br) (hOne : Br≤1) (qbar : ℕ) (hQ : 0<qbar)
    (X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false Bc) :
    let v := normalizedValues Qv hQv weights hPositive hWeights
    security v (Br:ℝ) (strategy false a k Qv hm hQv weights hWeights Bc Br hBc qbar)≤
      expected v (strategy true a k Qv hm hQv weights hWeights Bc Br hBr qbar) (physicalLaw X qbar)+
        ((GeneralPaperSourceParameters.prepare k).z:ℝ)/64 := by
  dsimp only
  apply GeneralPaperContinuousResponsePayoff.security_le_from_literal a Bc Br hBr hOne
    (GeneralPaperCatalogueChosenMixture.feasible_empirical false a k Qv hm hQv weights hWeights Bc Br hBc)
    qbar hm hQ (normalizedValues Qv hQv weights hPositive hWeights)
  intro Y
  have hg := canonical_gap a k Qv hm hQv weights hPositive hWeights Bc Br hBc hBr qbar hQ X Y
  dsimp only at hg
  change expected (normalizedValues Qv hQv weights hPositive hWeights) (physicalLaw Y qbar)
    (strategy false a k Qv hm hQv weights hWeights Bc Br hBc qbar)≤_
  linarith only [hg]

theorem security_compare {m : ℕ} (a : Alphabet) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hPositive : ∀ j, 0<weights.read j) (hWeights : ∑ j, weights.read j=Qv)
    (Bc Br : ℚ) (hBc : 0≤Bc) (hBr : 0≤Br) (hOne : Br≤1)
    (q qbar : ℕ) (hq : 0<q) (hCap : q≤qbar) (hDen : Br.den∣q)
    (X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false Bc) :
    let v := normalizedValues Qv hQv weights hPositive hWeights
    security v (Br:ℝ) (strategy false a k Qv hm hQv weights hWeights Bc Br hBc qbar)≤
      security v (Br:ℝ) (physicalLaw X qbar)+((GeneralPaperSourceParameters.prepare k).z:ℝ)/64 := by
  dsimp only
  have hQ : 0<qbar := lt_of_lt_of_le hq hCap
  have hu := continuous_upper a k Qv hm hQv weights hPositive hWeights Bc Br hBc hBr hOne qbar hQ X
  dsimp only at hu
  have hs := strategy_supported true a k Qv hm hQv weights hWeights Bc Br hBr q qbar hq hCap hDen
  have he := expected_le_security (normalizedValues Qv hQv weights hPositive hWeights)
    (strategy true a k Qv hm hQv weights hWeights Bc Br hBr qbar) (physicalLaw X qbar) hs
  simp only [ite_true] at he
  linarith only [hu,he]

end Blotto.GeneralPaperCatalogueContinuousSecurity
