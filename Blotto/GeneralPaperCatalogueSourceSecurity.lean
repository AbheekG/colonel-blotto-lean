import Blotto.GeneralPaperComparatorSecurity
import Blotto.GeneralPaperCatalogueContinuousSecurity

/-! Each actual deterministic full-trajectory source law is within z/32
of the continuous security infimum. The arbitrary original whole law is
embedded into the actual alphabet; no finite-response or convergence oracle
is supplied. The comparison uses an infimum, without assuming attainment.
-/
namespace Blotto.GeneralPaperCatalogueSourceSecurity
open GeneralPaperCodeAlphabet GeneralPaperCatalogueCanonicalGap GeneralPaperCodeMixturePhysical
open ContinuousSecurityValues
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem loss_bound {m : ℕ} (a : Alphabet) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hPositive : ∀ j, 0<weights.read j) (hWeights : ∑ j, weights.read j=Qv)
    (Bc Br : ℚ) (hBc : 0≤Bc ∧ Bc≤1) (hBr : 0≤Br ∧ Br≤1)
    (q qbar : ℕ) (hq : 0<q) (hCap : q≤qbar) (hDen : Br.den∣q)
    (hD : (Bc.den*Br.den)*(m+2)^(m*((GeneralPaperComparatorParameters.countRun k).power-1)+1)≤a.D) :
    let v := normalizedValues Qv hQv weights hPositive hWeights
    security v (Br:ℝ) (strategy false a k Qv hm hQv weights hWeights Bc Br hBc.1 qbar)≤
      lossInfimum v (Bc:ℝ) (Br:ℝ)+((GeneralPaperSourceParameters.prepare k).z:ℝ)/32 := by
  dsimp only
  let v := normalizedValues Qv hQv weights hPositive hWeights
  let result := strategy false a k Qv hm hQv weights hWeights Bc Br hBc.1 qbar
  have hInf : security v (Br:ℝ) result-((GeneralPaperSourceParameters.prepare k).z:ℝ)/32≤
      lossInfimum v (Bc:ℝ) (Br:ℝ) := by
    apply le_lossInfimum v (Bc:ℝ) (Br:ℝ) _ (by exact_mod_cast hBc.1)
    intro law hLaw
    have hd : RationalOrderCell.commonDenominator ![Bc,Br]*(m+2)^
        (m*((GeneralPaperComparatorParameters.countRun k).power-1)+1)≤a.D := by
      simpa only [RationalOrderCell.commonDenominator,Matrix.cons_val_zero,Matrix.cons_val_one] using hD
    obtain ⟨X,hCompare,hFinite⟩ := GeneralPaperRationalComparator.exists_code_comparator a v law ![Bc,Br] 0 1
      (by exact_mod_cast hBc.2) hLaw (by exact_mod_cast hBr.1)
      (GeneralPaperComparatorParameters.countRun k).power (GeneralPaperComparatorParameters.count_positive k) hd qbar
    have hSource := GeneralPaperCatalogueContinuousSecurity.security_compare a k Qv hm hQv weights hPositive hWeights
      Bc Br hBc.1 hBr.1 hBr.2 q qbar hq hCap hDen X
    dsimp only at hSource
    change security v (Br:ℝ) result≤security v (Br:ℝ) (physicalLaw X qbar)+_ at hSource
    change security v (Br:ℝ) (physicalLaw X qbar)≤security v (Br:ℝ) law+_ at hCompare
    rw [GeneralPaperComparatorParameters.count_error] at hCompare
    linarith
  change security v (Br:ℝ) result≤_
  linarith

end Blotto.GeneralPaperCatalogueSourceSecurity
