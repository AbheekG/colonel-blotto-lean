import Blotto.GeneralPaperInitializerPreparedPoint

/-! Nonroot auxiliary-budget interval for bounded integer affine residuals.
Every real zero forces a small-denominator rational root; the derived
4*tau separation excludes the whole CLOSED auxiliary interval. Constants
and identities remain distinct cases; beta0 nonvanishing is discharged
from actual constraint coefficients in the selected join.
-/
namespace Blotto.GeneralPaperInitializerIntervalRoots
open GeneralPaperInitializerParameters GeneralPaperInitializerRootGap GeneralPaperIntegerResidualRoots
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem nonzero_closed_interval (m H p q : ℕ) (reciprocal : Bool)
    (hm : 0<m) (hH : 0<H) (hp : 0<p) (hq : 0<q)
    (A B : ℤ) (hB : B≠0) (hBound : B.natAbs≤H)
    (hBeta : (A:ℚ)+(B:ℚ)*(prepare m H p q reciprocal).beta≠0)
    (gamma : ℝ) (hGamma : ((prepare m H p q reciprocal).auxiliary:ℝ)≤gamma ∧ gamma≤((prepare m H p q reciprocal).beta:ℝ)) :
    (A:ℝ)+(B:ℝ)*gamma≠0 := by
  intro he
  have hr := (real_affine_zero_iff A B hB gamma).mp he
  have hd := (root_denominator A B hB).trans hBound
  have hDifferent : (prepare m H p q reciprocal).beta≠root A B := by
    intro hh
    exact hBeta ((affine_zero_iff A B hB _).mpr hh)
  have hClosed : (prepare m H p q reciprocal).auxiliary≤root A B ∧ root A B≤(prepare m H p q reciprocal).beta := by
    rw [hr] at hGamma
    exact_mod_cast hGamma
  exact excludes_auxiliary_interval m H p q reciprocal hm hH hp hq _ hd hDifferent hClosed

end Blotto.GeneralPaperInitializerIntervalRoots
