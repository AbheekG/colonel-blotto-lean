import Blotto.GeneralPaperBasisAuxiliaryContinuation

/-! The actual classifier's root-free ratio paths cover all half-open
threshold intervals in the direction of modification. The poor branch
requires its endpoint to be positive before any reciprocal is formed.
-/
namespace Blotto.GeneralPaperBasisThresholdPaths
open GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem rich_nonzero (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .rich)
    (A B : ℤ) (hB : B≠0) (hBound : B.natAbs≤(prepare m k).H) (gamma : ℝ)
    (hGamma : ((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ)≤gamma ∧
      gamma<((GeneralPaperProxyClassifier.classify m k b).choice.endpoint:ℝ)) :
    (A:ℝ)+gamma*(B:ℝ)≠0 := by
  have hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none := by
    intro he
    rw [hModify] at he
    cases he
  by_cases he : gamma=((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ)
  · rw [he]
    have hh := GeneralPaperProxyResidualPaths.affine_proxy_nonzero m k b hb hm A B hB hBound
    have hr : (A:ℝ)+(B:ℝ)*((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ)≠0 := by exact_mod_cast hh
    simpa only [mul_comm] using hr
  · have hh := GeneralPaperProxyRealResidualPaths.affine_nonzero m k b hb hm A B hB hBound gamma
      (Or.inl ⟨lt_of_le_of_ne hGamma.1 (Ne.symm he),hGamma.2⟩)
    simpa only [mul_comm] using hh

theorem poor_nonzero (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor)
    (_hEndpoint : (0:ℝ)<(GeneralPaperProxyClassifier.classify m k b).choice.endpoint)
    (A B : ℤ) (hB : B≠0) (hBound : A.natAbs≤(prepare m k).H) (gamma : ℝ)
    (hGamma : 1/((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ)≤gamma ∧
      gamma<1/((GeneralPaperProxyClassifier.classify m k b).choice.endpoint:ℝ)) :
    (A:ℝ)+gamma*(B:ℝ)≠0 := by
  have hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none := by
    intro he
    rw [hModify] at he
    cases he
  have hp : (0:ℝ)<(GeneralPaperProxyClassifier.classify m k b).choice.proxy.value := by
    exact_mod_cast (GeneralPaperProxyClassifier.proxy_unit m k b hb).1
  by_cases he : gamma=1/((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ)
  · rw [he]
    have hh := GeneralPaperProxyResidualPaths.reciprocal_proxy_nonzero m k b hb hm A B hB hBound
    have hr : (A:ℝ)+(B:ℝ)/((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ)≠0 := by exact_mod_cast hh
    simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using hr
  · have hStrict : 1/((GeneralPaperProxyClassifier.classify m k b).choice.proxy.value:ℝ)<gamma :=
      lt_of_le_of_ne hGamma.1 (Ne.symm he)
    have hg : 0<gamma := (one_div_pos.mpr hp).trans hStrict
    have hLeft := one_div_lt_one_div_of_lt hg hGamma.2
    have hRight := one_div_lt_one_div_of_lt (one_div_pos.mpr hp) hStrict
    simp only [one_div_one_div] at hLeft hRight
    have hh := GeneralPaperProxyRealResidualPaths.reciprocal_nonzero m k b hb hm A B hB hBound (1/gamma)
      (Or.inr ⟨hLeft,hRight⟩)
    simpa only [one_div,div_eq_mul_inv,inv_inv,one_mul,mul_one,mul_comm] using hh

end Blotto.GeneralPaperBasisThresholdPaths
