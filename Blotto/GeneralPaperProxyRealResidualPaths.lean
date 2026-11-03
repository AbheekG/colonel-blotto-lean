import Blotto.GeneralPaperProxyResidualPaths

/-! The root-free path covers every REAL parameter, including the original
real budget. Vanishing of an affine integer residual forces a rational
root, so the executed classifier excludes it in both budget normalizations.
Coefficient bounds still require the actual constraint/matrix derivation.
-/
namespace Blotto.GeneralPaperProxyRealResidualPaths
open GeneralPaperProxyParameters GeneralPaperIntegerResidualRoots GeneralPaperProxySelection
set_option autoImplicit false
set_option maxHeartbeats 2500000

def BetweenReal (a e : ℚ) (x : ℝ) : Prop := ((a:ℝ)<x ∧ x<(e:ℝ)) ∨ ((e:ℝ)<x ∧ x<(a:ℝ))

theorem between_cast (a e x : ℚ) : BetweenReal a e (x:ℝ) ↔ GeneralPaperProxyCellPaths.Between a e x := by
  simp only [BetweenReal,GeneralPaperProxyCellPaths.Between,Rat.cast_lt]

theorem path_positive (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none) (x : ℝ)
    (hx : BetweenReal (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint x) : 0<x := by
  have hp : (0:ℝ)<(GeneralPaperProxyClassifier.classify m k b).choice.proxy.value :=
    by exact_mod_cast (GeneralPaperProxyClassifier.proxy_unit m k b hb).1
  have he : (0:ℝ)≤(GeneralPaperProxyClassifier.classify m k b).choice.endpoint :=
    by exact_mod_cast (GeneralPaperProxyEndpointBounds.endpoint_unit m k b hb hm).1
  rcases hx with ⟨h1,h2⟩|⟨h1,h2⟩
  · exact hp.trans h1
  · exact he.trans_lt h1

theorem affine_nonzero (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (A B : ℤ) (hB : B≠0) (hBound : B.natAbs≤(prepare m k).H) (x : ℝ)
    (hx : BetweenReal (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint x) : (A:ℝ)+(B:ℝ)*x≠0 := by
  intro he
  have hr := (real_affine_zero_iff A B hB x).mp he
  have hd := (root_denominator A B hB).trans hBound
  have hc : GeneralPaperProxyCellPaths.Between (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint (root A B) := by
    rw [hr] at hx
    exact (between_cast _ _ _).mp hx
  exact GeneralPaperProxyClassifierPaths.open_path m k b hb hm _ hd hc

theorem reciprocal_nonzero (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (A B : ℤ) (hB : B≠0) (hBound : A.natAbs≤(prepare m k).H) (x : ℝ)
    (hx : BetweenReal (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint x) : (A:ℝ)+(B:ℝ)/x≠0 := by
  have hx0 : x≠0 := (path_positive m k b hb hm x hx).ne'
  by_cases hA : A=0
  · subst A
    simp only [Int.cast_zero,zero_add]
    exact div_ne_zero (by exact_mod_cast hB) hx0
  · intro he
    have hr := (real_reciprocal_zero_iff A B hA x hx0).mp he
    have hd := (root_denominator B A hA).trans hBound
    have hc : GeneralPaperProxyCellPaths.Between (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
        (GeneralPaperProxyClassifier.classify m k b).choice.endpoint (root B A) := by
      rw [hr] at hx
      exact (between_cast _ _ _).mp hx
    exact GeneralPaperProxyClassifierPaths.open_path m k b hb hm _ hd hc

theorem original_budget_between (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none) :
    BetweenReal (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint b := by
  rcases GeneralPaperProxyClassifierPaths.safe m k b hb with hu|⟨hd,hp,hr|hb'⟩
  · exact (hm hu.1).elim
  · exact Or.inl hr.2
  · exact Or.inr hb'.2

theorem affine_original_budget (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (A B : ℤ) (hB : B≠0) (hBound : B.natAbs≤(prepare m k).H) : (A:ℝ)+(B:ℝ)*b≠0 :=
  affine_nonzero m k b hb hm A B hB hBound b (original_budget_between m k b hb hm)

theorem reciprocal_original_budget (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (hm : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (A B : ℤ) (hB : B≠0) (hBound : A.natAbs≤(prepare m k).H) : (A:ℝ)+(B:ℝ)/b≠0 :=
  reciprocal_nonzero m k b hb hm A B hB hBound b (original_budget_between m k b hb hm)

end Blotto.GeneralPaperProxyRealResidualPaths
