import Blotto.GeneralPaperProxyClassifier
import Blotto.GeneralPaperCatalogueQuantizedSource

/-! The actual pre-call classifier now supplies the proxy ratio and cap
to the selected geometric source. No ratio-denominator or alphabet oracle
remains in this source-security statement. Original-unit transfer along
the selected modification/endpoint, full prices and output remain open.
-/
namespace Blotto.GeneralPaperPreparedProxySource
open GeneralPaperCatalogueCanonicalGap GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def ratio (m k : ℕ) (b : ℝ) : ℚ := (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value

theorem ratio_valid (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) : 0<ratio m k b ∧ ratio m k b≤1 :=
  ⟨(GeneralPaperProxyClassifier.proxy_unit m k b hb).1,(GeneralPaperProxyClassifier.proxy_unit m k b hb).2.le⟩

theorem source {n : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable (n+1) ℕ)
    (hPositive : ∀ j, 0<weights.read j) (hWeights : ∑ j, weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) :
    let rho := ratio (n+1) k b
    let hr := ratio_valid (n+1) k b hb
    let a := alphabet (n+1) k
    let qbar := (prepare (n+1) k).qbar
    let v := normalizedValues Qv hQv weights hPositive hWeights
    let rich := strategy false a k Qv (by omega) hQv weights hWeights 1 rho (by norm_num) qbar
    let poor := strategy false a k Qv (by omega) hQv weights hWeights rho 1 hr.1.le qbar
    Supported 1 rich ∧ Supported (rho:ℝ) poor ∧
      security v (rho:ℝ) rich+security v 1 poor≤1+3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32 :=
  GeneralPaperCataloguePairedSecurity.paper_source k Qv (prepare (n+1) k).qbar (cap_positive (n+1) k)
    hQv weights hPositive hWeights (ratio (n+1) k b) (ratio_valid (n+1) k b hb)
    (GeneralPaperProxyClassifier.proxy_reduced_denominator (n+1) k b)

theorem quantized_source {n : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable (n+1) ℕ)
    (hPositive : ∀ j, 0<weights.read j) (hWeights : ∑ j, weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) :
    let rho := ratio (n+1) k b
    let a := alphabet (n+1) k
    let qbar := (prepare (n+1) k).qbar
    let hT := GeneralPaperTrajectoryParameters.rows_positive a.lambda k
    let v := normalizedValues Qv hQv weights hPositive hWeights
    security v (rho:ℝ) (GeneralPaperDictionary.law
        (GeneralPaperCatalogueQuantizedSource.dictionary a k Qv qbar weights 1 rho) hT).law+
      security v 1 (GeneralPaperDictionary.law
        (GeneralPaperCatalogueQuantizedSource.dictionary a k Qv qbar weights rho 1) hT).law≤
      1+3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32+2/((prepare (n+1) k).K:ℝ) :=
  GeneralPaperCatalogueQuantizedSource.paired_security k Qv (prepare (n+1) k).qbar (cap_positive (n+1) k)
    hQv weights hPositive hWeights (ratio (n+1) k b) (ratio_valid (n+1) k b hb)
    (GeneralPaperProxyClassifier.proxy_reduced_denominator (n+1) k b)

end Blotto.GeneralPaperPreparedProxySource
