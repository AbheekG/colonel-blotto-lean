import Blotto.GeneralPaperRoundedValuePerturbation

/-! Canonical reduced-input equilibrium after native value rounding. The
actual returned integer weights feed the selected source/compiler pair.
Its two independent whole-player laws have hard budgets and continuous
Nash regrets for the unrounded reduced values strictly below e/16. This is
the semantic join; complete native driver prices and original-field circle
lifting remain separate obligations. -/
namespace Blotto.GeneralPaperRoundedValueCanonical
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

noncomputable def run {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j) (b : ℝ) :=
  let rounded := (GeneralPaperValueRoundingPaperContract.run bits model W 512 k values).1
  let hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 512 k (by decide) values v hv
  GeneralPaperSourcePairRun.run k rounded.2 hp.1 rounded.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum bits model W 512 k values) b

theorem run_regrets {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j)
    (b : ℝ) (hb : 0<b ∧ b<1) :
    let rounded := (GeneralPaperValueRoundingPaperContract.run bits model W 512 k values).1
    let hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 512 k (by decide) values v hv
    let hT := GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet m k).lambda k
    ∃ pair,run bits model W k values v hv b=some pair ∧
      GeneralPaperSourcePairContract.Contract k rounded.2 hp.1 rounded.1 hp.2
        (GeneralPaperValueRoundingPaperContract.source_sum bits model W 512 k values) b pair ∧
      Supported 1 (GeneralPaperSourcePairCanonical.richLaw pair hT) ∧
      Supported b (GeneralPaperSourcePairCanonical.poorLaw pair hT b) ∧
      regret v.values 1 (GeneralPaperSourcePairCanonical.richLaw pair hT)
        (GeneralPaperSourcePairCanonical.poorLaw pair hT b)<(1/(2:ℝ)^k)/16 ∧
      regret v.values b (GeneralPaperSourcePairCanonical.poorLaw pair hT b)
        (GeneralPaperSourcePairCanonical.richLaw pair hT)<(1/(2:ℝ)^k)/16 := by
  dsimp only
  let rounded := (GeneralPaperValueRoundingPaperContract.run bits model W 512 k values).1
  have hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 512 k (by decide) values v hv
  have hs := GeneralPaperValueRoundingPaperContract.source_sum bits model W 512 k values
  have hT := GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet m k).lambda k
  obtain ⟨pair,hRun,hc,hA,hB,hRA,hRB⟩ := GeneralPaperSourcePairCanonical.run_regrets k rounded.2
    v.fields_positive hp.1 rounded.1 hp.2 hs b hb
  refine ⟨pair,hRun,hc,hA,hB,?_,?_⟩
  · have hr := GeneralPaperRoundedValuePerturbation.reduced_regret bits model W k values v hv 1
      (by norm_num) (GeneralPaperSourcePairCanonical.richLaw pair hT)
      (GeneralPaperSourcePairCanonical.poorLaw pair hT b)
    exact (hr.trans (add_le_add hRA (le_refl _))).trans_lt
      (GeneralPaperRoundedValuePerturbation.reduced_gap m k v.fields_positive)
  · have hr := GeneralPaperRoundedValuePerturbation.reduced_regret bits model W k values v hv b hb.1.le
      (GeneralPaperSourcePairCanonical.poorLaw pair hT b)
      (GeneralPaperSourcePairCanonical.richLaw pair hT)
    exact (hr.trans (add_le_add hRB (le_refl _))).trans_lt
      (GeneralPaperRoundedValuePerturbation.reduced_gap m k v.fields_positive)

theorem run_security {m : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j)
    (b : ℝ) (hb : 0<b ∧ b<1) :
    let hT := GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet m k).lambda k
    ∃ pair,run bits model W k values v hv b=some pair ∧
      Supported 1 (GeneralPaperSourcePairCanonical.richLaw pair hT) ∧
      Supported b (GeneralPaperSourcePairCanonical.poorLaw pair hT b) ∧
      security v.values 1 (GeneralPaperSourcePairCanonical.poorLaw pair hT b)+
        security v.values b (GeneralPaperSourcePairCanonical.richLaw pair hT)<1+(1/(2:ℝ)^k)/16 ∧
      regret v.values 1 (GeneralPaperSourcePairCanonical.richLaw pair hT)
          (GeneralPaperSourcePairCanonical.poorLaw pair hT b)+
        regret v.values b (GeneralPaperSourcePairCanonical.poorLaw pair hT b)
          (GeneralPaperSourcePairCanonical.richLaw pair hT)<(1/(2:ℝ)^k)/16 := by
  dsimp only
  let rounded := (GeneralPaperValueRoundingPaperContract.run bits model W 512 k values).1
  have hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 512 k (by decide) values v hv
  have hs := GeneralPaperValueRoundingPaperContract.source_sum bits model W 512 k values
  have hT := GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet m k).lambda k
  let w := GeneralPaperRoundedValuePerturbation.selector bits model W 512 k (by decide) values v hv
  obtain ⟨pair,hRun,hc,hSec⟩ := GeneralPaperSourcePairSound.paired_security k rounded.2
    v.fields_positive hp.1 rounded.1 hp.2 hs b hb
  have hScale := security_scale w.values hb.1 (1/b) (GeneralPaperDictionary.law pair.poor hT).law
  have he : b*(1/b)=1 := by field_simp [hb.1.ne']
  rw [he] at hScale
  have hActual : security w.values 1 (GeneralPaperSourcePairCanonical.poorLaw pair hT b)+
      security w.values b (GeneralPaperSourcePairCanonical.richLaw pair hT)≤
      1+(3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32+
        2/((GeneralPaperProxyParameters.prepare m k).K:ℝ)+(m:ℝ)/(GeneralPaperProxyParameters.prepare m k).S) := by
    unfold GeneralPaperSourcePairCanonical.richLaw GeneralPaperSourcePairCanonical.poorLaw
    rw [hScale]
    change security w.values b (GeneralPaperDictionary.law pair.rich hT).law+
      security w.values (1/b) (GeneralPaperDictionary.law pair.poor hT).law≤_ at hSec
    linarith only [hSec]
  have hA := GeneralPaperValuePerturbation.security_le_shift v.values w.values 1 (by norm_num)
    (GeneralPaperSourcePairCanonical.poorLaw pair hT b)
  have hB := GeneralPaperValuePerturbation.security_le_shift v.values w.values b hb.1.le
    (GeneralPaperSourcePairCanonical.richLaw pair hT)
  have hd := GeneralPaperRoundedValuePerturbation.reduced_distance bits model W k values v hv
  have hg := GeneralPaperRoundedValuePerturbation.reduced_gap m k v.fields_positive
  have hFinal : security v.values 1 (GeneralPaperSourcePairCanonical.poorLaw pair hT b)+
      security v.values b (GeneralPaperSourcePairCanonical.richLaw pair hT)<1+(1/(2:ℝ)^k)/16 := by
    linarith only [hA,hB,hd,hActual,hg]
  have hSuppB := scaleLaw_supported hb.1.le (GeneralPaperDictionary.law pair.poor hT).law hc.poor_unit.supported
  have hSuppB' : Supported b (GeneralPaperSourcePairCanonical.poorLaw pair hT b) := by
    simpa only [GeneralPaperSourcePairCanonical.poorLaw,mul_one] using hSuppB
  refine ⟨pair,hRun,hc.rich_unit.supported,hSuppB',hFinal,?_⟩
  rw [regret_sum]
  linarith only [hFinal]

end Blotto.GeneralPaperRoundedValueCanonical
