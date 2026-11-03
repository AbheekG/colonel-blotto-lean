import Blotto.GeneralPaperInitializerIntervalRoots

/-! The auxiliary interval is root-free for the ACTUAL transfer subsystem
coefficients. Both beta0 nonvanishing and the uniform H bounds come from
the actual classifier and bordered matrices, not supplied root or gap data.
-/
namespace Blotto.GeneralPaperInitializerActualRoots
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperTransferResidualCoefficients
open GeneralPaperInitializerSelectedControls
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem beta_nonzero {T m : ℕ} (k : ℕ) (hm : 0<m)
    (labels : Fin T → Fin m → Fin (GeneralPaperProxyParameters.prepare m k).K)
    (scores : Fin m → Fin (GeneralPaperProxyParameters.prepare m k).K → ℕ) (h : ℕ)
    (selected : Variable m (GeneralPaperProxyParameters.prepare m k).K → Index T m (GeneralPaperProxyParameters.prepare m k).K scores h)
    (extra : Index T m (GeneralPaperProxyParameters.prepare m k).K scores h)
    (hB : (coefficients labels scores h selected extra).2≠0)
    (b : ℝ) (hb : 0<b ∧ b<1) (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (reciprocal : Bool) :
    ((coefficients labels scores h selected extra).1:ℚ)+
      ((coefficients labels scores h selected extra).2:ℚ)*(controls m k b reciprocal).beta≠0 := by
  have hc := coefficient_H k hm labels scores h selected extra
  rw [beta_value]
  cases reciprocal with
  | false =>
    exact GeneralPaperProxyResidualPaths.affine_proxy_nonzero m k b hb hModify _ _ hB hc.2.le
  | true =>
    have hn := GeneralPaperProxyResidualPaths.reciprocal_proxy_nonzero m k b hb hModify
      (coefficients labels scores h selected extra).1 (coefficients labels scores h selected extra).2 hB hc.1.le
    simpa only [ite_true,one_div,div_eq_mul_inv,mul_comm,one_mul,mul_one] using hn

theorem closed_interval_nonzero {T m : ℕ} (k : ℕ) (hm : 0<m)
    (labels : Fin T → Fin m → Fin (GeneralPaperProxyParameters.prepare m k).K)
    (scores : Fin m → Fin (GeneralPaperProxyParameters.prepare m k).K → ℕ) (h : ℕ)
    (selected : Variable m (GeneralPaperProxyParameters.prepare m k).K → Index T m (GeneralPaperProxyParameters.prepare m k).K scores h)
    (extra : Index T m (GeneralPaperProxyParameters.prepare m k).K scores h)
    (hB : (coefficients labels scores h selected extra).2≠0)
    (b : ℝ) (hb : 0<b ∧ b<1) (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (reciprocal : Bool) (gamma : ℝ)
    (hGamma : ((controls m k b reciprocal).auxiliary:ℝ)≤gamma ∧ gamma≤((controls m k b reciprocal).beta:ℝ)) :
    ((coefficients labels scores h selected extra).1:ℝ)+gamma*((coefficients labels scores h selected extra).2:ℝ)≠0 := by
  have hp := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hc := coefficient_H k hm labels scores h selected extra
  have hn := GeneralPaperInitializerIntervalRoots.nonzero_closed_interval m (GeneralPaperProxyParameters.prepare m k).H
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den reciprocal
    hm (GeneralPaperProxyParameters.H_positive m k) hp.1 (by omega) _ _ hB hc.2.le
    (beta_nonzero k hm labels scores h selected extra hB b hb hModify reciprocal) gamma hGamma
  simpa only [mul_comm] using hn

end Blotto.GeneralPaperInitializerActualRoots
