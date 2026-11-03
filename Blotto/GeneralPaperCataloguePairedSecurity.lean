import Blotto.GeneralPaperCatalogueSourceSecurity
import Blotto.UnitSecurityMinimax

/-! Continuous security of BOTH actual selected geometric source runs,
in the constructed alphabet. The cap qbar is supplied by the later proxy
constructor; its only semantic requirement here is ratio.den<=qbar.
The conclusion implies the paper's eq:general:source, including ratio=1
and one battlefield. Full source costs and the outer compiler remain open.
-/
namespace Blotto.GeneralPaperCataloguePairedSecurity
open GeneralPaperCatalogueCanonicalGap GeneralPaperComparatorParameters
open ContinuousSecurityValues
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem paired_security {n : ℕ} (k Qv qbar : ℕ) (hqbar : 0<qbar) (hQv : 0<Qv)
    (weights : FixedArrayTable (n+1) ℕ) (hPositive : ∀ j, 0<weights.read j) (hWeights : ∑ j, weights.read j=Qv)
    (ratio : ℚ) (hr : 0<ratio ∧ ratio≤1) (hCap : ratio.den≤qbar) :
    let a := alphabet (n+1) k qbar hqbar
    let v := normalizedValues Qv hQv weights hPositive hWeights
    let rich := strategy false a k Qv (by omega) hQv weights hWeights 1 ratio (by norm_num) qbar
    let poor := strategy false a k Qv (by omega) hQv weights hWeights ratio 1 hr.1.le qbar
    Supported 1 rich ∧ Supported (ratio:ℝ) poor ∧
      security v (ratio:ℝ) rich+security v 1 poor≤1+((GeneralPaperSourceParameters.prepare k).z:ℝ)/16 := by
  dsimp only
  let a := alphabet (n+1) k qbar hqbar
  let v := normalizedValues Qv hQv weights hPositive hWeights
  have hd := denominator_cap (n+1) k ratio.den qbar hqbar hCap
  have hdRich : ((1:ℚ).den*ratio.den)*(n+1+2)^((n+1)*((countRun k).power-1)+1)≤a.D := by
    simpa only [Rat.den_one,one_mul] using hd
  have hdPoor : (ratio.den*(1:ℚ).den)*(n+1+2)^((n+1)*((countRun k).power-1)+1)≤a.D := by
    simpa only [Rat.den_one,mul_one] using hd
  have hRich := GeneralPaperCatalogueSourceSecurity.loss_bound a k Qv (by omega) hQv weights hPositive hWeights
    1 ratio (by norm_num) ⟨hr.1.le,hr.2⟩ ratio.den qbar (Rat.den_pos ratio) hCap (dvd_refl _) hdRich
  have hPoor := GeneralPaperCatalogueSourceSecurity.loss_bound a k Qv (by omega) hQv weights hPositive hWeights
    ratio 1 ⟨hr.1.le,hr.2⟩ (by norm_num) ratio.den qbar (Rat.den_pos ratio) hCap (by simp) hdPoor
  dsimp only at hRich hPoor
  have hMinimax := UnitSecurityMinimax.lossInfimum_sum_eq_one v (ratio:ℝ)
    ⟨by exact_mod_cast hr.1,by exact_mod_cast hr.2⟩
  have hRichSupported := strategy_supported false a k Qv (by omega) hQv weights hWeights 1 ratio
    (by norm_num) ratio.den qbar (Rat.den_pos ratio) hCap (by simp)
  have hPoorSupported := strategy_supported false a k Qv (by omega) hQv weights hWeights ratio 1
    hr.1.le ratio.den qbar (Rat.den_pos ratio) hCap (dvd_refl _)
  simp only [Bool.false_eq_true,ite_false,Rat.cast_one] at hRichSupported hPoorSupported
  refine ⟨hRichSupported,hPoorSupported,?_⟩
  change security v (ratio:ℝ) _+security v 1 _≤_
  linarith only [hRich,hPoor,hMinimax]

theorem paper_source {n : ℕ} (k Qv qbar : ℕ) (hqbar : 0<qbar) (hQv : 0<Qv)
    (weights : FixedArrayTable (n+1) ℕ) (hPositive : ∀ j, 0<weights.read j) (hWeights : ∑ j, weights.read j=Qv)
    (ratio : ℚ) (hr : 0<ratio ∧ ratio≤1) (hCap : ratio.den≤qbar) :
    let a := alphabet (n+1) k qbar hqbar
    let v := normalizedValues Qv hQv weights hPositive hWeights
    let rich := strategy false a k Qv (by omega) hQv weights hWeights 1 ratio (by norm_num) qbar
    let poor := strategy false a k Qv (by omega) hQv weights hWeights ratio 1 hr.1.le qbar
    Supported 1 rich ∧ Supported (ratio:ℝ) poor ∧
      security v (ratio:ℝ) rich+security v 1 poor≤1+3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32 := by
  have hp := paired_security k Qv qbar hqbar hQv weights hPositive hWeights ratio hr hCap
  dsimp only at hp ⊢
  have hz : (0:ℝ)<(GeneralPaperSourceParameters.prepare k).z :=
    by exact_mod_cast (GeneralPaperSourceParameters.positive k).1
  exact ⟨hp.1,hp.2.1,by linarith [hp.2.2]⟩

theorem proxy_regrets {n : ℕ} (k Qv qbar : ℕ) (hqbar : 0<qbar) (hQv : 0<Qv)
    (weights : FixedArrayTable (n+1) ℕ) (hPositive : ∀ j, 0<weights.read j) (hWeights : ∑ j, weights.read j=Qv)
    (ratio : ℚ) (hr : 0<ratio ∧ ratio≤1) (hCap : ratio.den≤qbar) :
    let a := alphabet (n+1) k qbar hqbar
    let v := normalizedValues Qv hQv weights hPositive hWeights
    let rich := strategy false a k Qv (by omega) hQv weights hWeights 1 ratio (by norm_num) qbar
    let poor := strategy false a k Qv (by omega) hQv weights hWeights ratio 1 hr.1.le qbar
    regret v 1 rich poor≤3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32 ∧
      regret v (ratio:ℝ) poor rich≤3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32 := by
  have hp := paper_source k Qv qbar hqbar hQv weights hPositive hWeights ratio hr hCap
  dsimp only at hp ⊢
  apply regrets_le_of_security_sum _ _ _ hp.1 hp.2.1
  linarith only [hp.2.2]

end Blotto.GeneralPaperCataloguePairedSecurity
