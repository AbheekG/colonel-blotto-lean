import Blotto.GeneralPaperBasisIntervalFeasibility

/-! Actual initializer threshold identities and order in real units.
Both normalizations use the classifier's original unreduced integers.
-/
namespace Blotto.GeneralPaperBasisContinuationControls
open GeneralPaperInitializerSelectedControls GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem auxiliary_value (m k : ℕ) (hm : 0<m) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    (GeneralPaperBasisGridInputs.auxiliaryNumerator m (prepare m k).H
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den reciprocal:ℝ)/(controls m k b reciprocal).N=
        ((controls m k b reciprocal).auxiliary:ℝ) := by
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hh := congrArg (fun r : ℚ => (r:ℝ))
    (GeneralPaperBasisGridInputs.auxiliary_decode m (prepare m k).H
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den reciprocal hm (H_positive m k) hf.1 (by omega))
  unfold controls
  simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using hh

theorem beta_real (m k : ℕ) (b : ℝ) (reciprocal : Bool) :
    ((controls m k b reciprocal).beta:ℝ)=
      if reciprocal then 1/((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ)
        else ((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ) := by
  have hh := congrArg (fun r : ℚ => (r:ℝ)) (beta_value m k b reciprocal)
  cases reciprocal <;> simpa only [Bool.false_eq_true,ite_false,ite_true,Rat.cast_div,Rat.cast_one] using hh

theorem auxiliary_le_beta (m k : ℕ) (hm : 0<m) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    ((controls m k b reciprocal).auxiliary:ℝ)≤((controls m k b reciprocal).beta:ℝ) := by
  have hh : (controls m k b reciprocal).auxiliary≤(controls m k b reciprocal).beta := by
    change (controls m k b reciprocal).beta-(controls m k b reciprocal).tau≤(controls m k b reciprocal).beta
    exact sub_le_self _ (positive m k hm b hb reciprocal).2.1.le
  exact_mod_cast hh

end Blotto.GeneralPaperBasisContinuationControls
