import Blotto.GeneralPaperProxyEndpointBounds

/-! Bounded affine integer residuals do not vanish at the actual modified
proxy or on its open path, in either defender's normalization. Constant
residuals and identities are separated explicitly. Actual determinant and
constraint-row coefficient bounds remain the next required matrix join.
-/
namespace Blotto.GeneralPaperProxyResidualPaths
open GeneralPaperProxyParameters GeneralPaperIntegerResidualRoots
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem affine_proxy_nonzero (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (A B : ℤ) (hB : B≠0) (hBound : B.natAbs≤(prepare m k).H) :
    (A:ℚ)+(B:ℚ)*(GeneralPaperProxyClassifier.classify m k b).choice.proxy.value≠0 :=
  affine_nonroot _ _ (GeneralPaperProxyClassifierPaths.denominator_large m k b hb hm) A B hB hBound

theorem reciprocal_proxy_nonzero (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (A B : ℤ) (hB : B≠0) (hBound : A.natAbs≤(prepare m k).H) :
    (A:ℚ)+(B:ℚ)/(GeneralPaperProxyClassifier.classify m k b).choice.proxy.value≠0 :=
  reciprocal_nonroot _ _ (GeneralPaperProxyClassifierPaths.denominator_large m k b hb hm)
    (GeneralPaperProxyClassifier.proxy_unit m k b hb).1.ne' A B hB hBound

theorem affine_path_nonzero (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (A B : ℤ) (hB : B≠0) (hBound : B.natAbs≤(prepare m k).H) (x : ℚ)
    (hx : GeneralPaperProxyCellPaths.Between (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint x) : (A:ℚ)+(B:ℚ)*x≠0 := by
  intro he
  have hr := (affine_zero_iff A B hB x).mp he
  have hd : x.den≤(prepare m k).H := by rw [hr]; exact (root_denominator A B hB).trans hBound
  exact GeneralPaperProxyClassifierPaths.open_path m k b hb hm x hd hx

theorem reciprocal_path_nonzero (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (A B : ℤ) (hB : B≠0) (hBound : A.natAbs≤(prepare m k).H) (x : ℚ)
    (hx : GeneralPaperProxyCellPaths.Between (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint x) : (A:ℚ)+(B:ℚ)/x≠0 := by
  have hx0 : x≠0 := (GeneralPaperProxyEndpointBounds.open_path_positive m k b hb hm x hx).ne'
  by_cases hA : A=0
  · subst A
    simp only [Int.cast_zero,zero_add]
    exact div_ne_zero (by exact_mod_cast hB) hx0
  · intro he
    have hr := (reciprocal_zero_iff A B hA x hx0).mp he
    have hd : x.den≤(prepare m k).H := by rw [hr]; exact (root_denominator B A hA).trans hBound
    exact GeneralPaperProxyClassifierPaths.open_path m k b hb hm x hd hx

theorem constant_nonzero (A : ℤ) (hA : A≠0) (x : ℚ) : (A:ℚ)+(0:ℚ)*x≠0 := by
  simpa only [zero_mul,add_zero] using (show (A:ℚ)≠0 by exact_mod_cast hA)

theorem identity (x : ℚ) : (0:ℚ)+(0:ℚ)*x=0 := by ring

end Blotto.GeneralPaperProxyResidualPaths
