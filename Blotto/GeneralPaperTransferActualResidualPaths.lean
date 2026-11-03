import Blotto.GeneralPaperTransferResidualCoefficients

/-! The classifier's nonroot/path guarantees now apply to residuals of
the ACTUAL transfer constraint subsystem. Integer coefficient bounds come
from its bordered matrices, not an oracle. The point is any solution of
the selected equations; constructing the original-basis continuation is
still required. Reciprocal normalization is confined to positive points.
-/
namespace Blotto.GeneralPaperTransferActualResidualPaths
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperTransferResidualCoefficients
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem residual_nonzero {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h)
    (extra : Index T m K scores h) (gamma : ℝ) (x : Variable m K → ℝ)
    (hSystem : ∀ i,(constraints labels scores h (selected i)).linear.evaluate x=
      (constraints labels scores h (selected i)).bound gamma)
    (hPoly : ((coefficients labels scores h selected extra).1:ℝ)+
      gamma*((coefficients labels scores h selected extra).2:ℝ)≠0) :
    (constraints labels scores h extra).linear.evaluate x-(constraints labels scores h extra).bound gamma≠0 := by
  intro he
  have hi := residual_identity labels scores h selected extra gamma x hSystem
  rw [he,mul_zero] at hi
  exact hPoly hi.symm

theorem constant_residual_nonzero {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h)
    (extra : Index T m K scores h) (gamma : ℝ) (x : Variable m K → ℝ)
    (hSystem : ∀ i,(constraints labels scores h (selected i)).linear.evaluate x=
      (constraints labels scores h (selected i)).bound gamma)
    (hA : (coefficients labels scores h selected extra).1≠0)
    (hB : (coefficients labels scores h selected extra).2=0) :
    (constraints labels scores h extra).linear.evaluate x-(constraints labels scores h extra).bound gamma≠0 := by
  apply residual_nonzero labels scores h selected extra gamma x hSystem
  simp only [hB,Int.cast_zero,mul_zero,add_zero]
  exact_mod_cast hA

theorem identity_residual_zero {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h)
    (extra : Index T m K scores h) (gamma : ℝ) (x : Variable m K → ℝ)
    (hSystem : ∀ i,(constraints labels scores h (selected i)).linear.evaluate x=
      (constraints labels scores h (selected i)).bound gamma)
    (hDet : (GeneralPaperTransferMatrices.matrix labels scores h selected).det≠0)
    (hA : (coefficients labels scores h selected extra).1=0)
    (hB : (coefficients labels scores h selected extra).2=0) :
    (constraints labels scores h extra).linear.evaluate x-(constraints labels scores h extra).bound gamma=0 := by
  have hi := residual_identity labels scores h selected extra gamma x hSystem
  simp only [hA,hB,Int.cast_zero,mul_zero,add_zero] at hi
  exact (mul_eq_zero.mp hi).resolve_left (by exact_mod_cast hDet)

theorem actual_path {T m : ℕ} (k : ℕ) (hm : 0<m)
    (labels : Fin T → Fin m → Fin (GeneralPaperProxyParameters.prepare m k).K)
    (scores : Fin m → Fin (GeneralPaperProxyParameters.prepare m k).K → ℕ) (h : ℕ)
    (selected : Variable m (GeneralPaperProxyParameters.prepare m k).K →
      Index T m (GeneralPaperProxyParameters.prepare m k).K scores h)
    (extra : Index T m (GeneralPaperProxyParameters.prepare m k).K scores h)
    (hNonconstant : (coefficients labels scores h selected extra).2≠0)
    (b : ℝ) (hb : 0<b ∧ b<1) (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (t : ℝ) (hPath : GeneralPaperProxyRealResidualPaths.BetweenReal
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value (GeneralPaperProxyClassifier.classify m k b).choice.endpoint t)
    (reciprocal : Bool) (x : Variable m (GeneralPaperProxyParameters.prepare m k).K → ℝ)
    (hSystem : ∀ i,(constraints labels scores h (selected i)).linear.evaluate x=
      (constraints labels scores h (selected i)).bound (if reciprocal then 1/t else t)) :
    (constraints labels scores h extra).linear.evaluate x-
      (constraints labels scores h extra).bound (if reciprocal then 1/t else t)≠0 := by
  apply residual_nonzero labels scores h selected extra _ x hSystem
  have hc := coefficient_H k hm labels scores h selected extra
  cases reciprocal with
  | false =>
    have hn := GeneralPaperProxyRealResidualPaths.affine_nonzero m k b hb hModify
      (coefficients labels scores h selected extra).1 (coefficients labels scores h selected extra).2 hNonconstant hc.2.le t hPath
    simpa only [Bool.false_eq_true,ite_false,mul_comm] using hn
  | true =>
    have hn := GeneralPaperProxyRealResidualPaths.reciprocal_nonzero m k b hb hModify
      (coefficients labels scores h selected extra).1 (coefficients labels scores h selected extra).2 hNonconstant hc.1.le t hPath
    simpa only [ite_true,one_div,div_eq_mul_inv,mul_comm,one_mul,mul_one] using hn

theorem actual_proxy {T m : ℕ} (k : ℕ) (hm : 0<m)
    (labels : Fin T → Fin m → Fin (GeneralPaperProxyParameters.prepare m k).K)
    (scores : Fin m → Fin (GeneralPaperProxyParameters.prepare m k).K → ℕ) (h : ℕ)
    (selected : Variable m (GeneralPaperProxyParameters.prepare m k).K →
      Index T m (GeneralPaperProxyParameters.prepare m k).K scores h)
    (extra : Index T m (GeneralPaperProxyParameters.prepare m k).K scores h)
    (hNonconstant : (coefficients labels scores h selected extra).2≠0)
    (b : ℝ) (hb : 0<b ∧ b<1) (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (reciprocal : Bool) (x : Variable m (GeneralPaperProxyParameters.prepare m k).K → ℝ)
    (hSystem : ∀ i,(constraints labels scores h (selected i)).linear.evaluate x=
      (constraints labels scores h (selected i)).bound
        (if reciprocal then 1/((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ)
          else ((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ))) :
    (constraints labels scores h extra).linear.evaluate x-
      (constraints labels scores h extra).bound
        (if reciprocal then 1/((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ)
          else ((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ))≠0 := by
  apply residual_nonzero labels scores h selected extra _ x hSystem
  have hc := coefficient_H k hm labels scores h selected extra
  cases reciprocal with
  | false =>
    have hn := GeneralPaperProxyResidualPaths.affine_proxy_nonzero m k b hb hModify
      (coefficients labels scores h selected extra).1 (coefficients labels scores h selected extra).2 hNonconstant hc.2.le
    have hr : ((coefficients labels scores h selected extra).1:ℝ)+
        ((coefficients labels scores h selected extra).2:ℝ)*
          ((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ)≠0 := by exact_mod_cast hn
    simpa only [Bool.false_eq_true,ite_false,mul_comm] using hr
  | true =>
    have hn := GeneralPaperProxyResidualPaths.reciprocal_proxy_nonzero m k b hb hModify
      (coefficients labels scores h selected extra).1 (coefficients labels scores h selected extra).2 hNonconstant hc.1.le
    have hr : ((coefficients labels scores h selected extra).1:ℝ)+
        ((coefficients labels scores h selected extra).2:ℝ)/
          ((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ)≠0 := by exact_mod_cast hn
    simpa only [ite_true,one_div,div_eq_mul_inv,mul_comm,one_mul,mul_one] using hr

end Blotto.GeneralPaperTransferActualResidualPaths
