import Blotto.GeneralPaperInitializerDictionary

/-! The actual pre-call classifier supplies the initializer integers and
cap. All positive/unit/proxy premises of the N/tau/auxiliary constructor
are discharged internally. The original real input is never re-encoded.
-/
namespace Blotto.GeneralPaperInitializerSelectedControls
open GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def controls (m k : ℕ) (b : ℝ) (reciprocal : Bool) : GeneralPaperInitializerParameters.Parameters :=
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  GeneralPaperInitializerParameters.prepare m (prepare m k).H f.num f.den reciprocal

theorem positive (m k : ℕ) (hm : 0<m) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    0<(controls m k b reciprocal).N ∧ 0<(controls m k b reciprocal).tau ∧ 0<(controls m k b reciprocal).auxiliary := by
  have hp := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  exact ⟨GeneralPaperInitializerParameters.N_positive _ _ _ _ reciprocal hm (H_positive m k) hp.1 (by omega),
    GeneralPaperInitializerParameters.tau_positive _ _ _ _ reciprocal hm (H_positive m k) hp.1 (by omega),
    GeneralPaperInitializerParameters.auxiliary_positive _ _ _ _ reciprocal hm (H_positive m k) hp.1 (by omega)⟩

theorem beta_value (m k : ℕ) (b : ℝ) (reciprocal : Bool) :
    (controls m k b reciprocal).beta=
      if reciprocal then 1/(GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
        else (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value := by
  cases reciprocal <;> simp only [controls,GeneralPaperInitializerParameters.prepare,Farey.Fraction.value,
    Bool.false_eq_true,ite_false,ite_true,one_div,inv_div]

theorem depth_cap (m k : ℕ) (b : ℝ) (reciprocal : Bool) :
    (controls m k b reciprocal).N<2^(controls m k b reciprocal).depth :=
  GeneralPaperInitializerParameters.quotient_cap _ _ _ _ reciprocal

theorem N_width (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    binaryWordWidth (controls m k b reciprocal).N≤3+binaryWordWidth m+
      binaryWordWidth (prepare m k).H+2*binaryWordWidth (prepare m k).qbar := by
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  have hp := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hpCap : f.num≤(prepare m k).qbar := hp.2.1.le.trans hp.2.2
  have hqCap : f.den≤(prepare m k).qbar := hp.2.2
  have h1 := binaryWordWidth_mul 4 m
  have h2 := binaryWordWidth_mul (4*m) (prepare m k).H
  have h3 := binaryWordWidth_mul (4*m*(prepare m k).H) f.num
  have h4 := binaryWordWidth_mul (4*m*(prepare m k).H*f.num) f.den
  have h4w : binaryWordWidth 4=3 := by decide
  have hpw := binaryWordWidth_mono hpCap
  have hqw := binaryWordWidth_mono hqCap
  change binaryWordWidth (4*m*(prepare m k).H*f.num*f.den)≤_
  omega

theorem depth_width (m k : ℕ) (b : ℝ) (reciprocal : Bool) :
    (controls m k b reciprocal).depth≤binaryWordWidth (controls m k b reciprocal).N+1 := by
  have hd := GeneralPaperPowerCeiling.loop_depth (controls m k b reciprocal).N 1 (by decide)
  change (GeneralPaperPowerCeiling.ceiling (controls m k b reciprocal).N).doublings≤_ at hd
  change (GeneralPaperPowerCeiling.ceiling (controls m k b reciprocal).N).doublings+1≤_
  omega

end Blotto.GeneralPaperInitializerSelectedControls
