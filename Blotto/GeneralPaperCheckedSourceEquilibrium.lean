import Blotto.GeneralPaperCheckedSourcePair

/-! Both canonical continuous regrets of the executed algorithm WITH
its auxiliary/endpoint rechecks. The rational accuracy input selects the
same dyadic parameters. Scope remains the normalized integer-value game.
-/
namespace Blotto.GeneralPaperCheckedSourceEquilibrium
open GeneralPaperProxyParameters GeneralPaperCheckedSourcePair GeneralPaperSourcePairCanonical
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem run_regrets {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) :
    ∃ pair,run k Qv hQv weights hp hs b=some pair ∧ GeneralPaperSourcePairContract.Contract k Qv hQv weights hp hs b pair ∧
      Supported 1 (richLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)) ∧
      Supported b (poorLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) b) ∧
      regret (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values 1
        (richLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k))
        (poorLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) b)≤
          3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32+2/((prepare m k).K:ℝ)+(m:ℝ)/(prepare m k).S ∧
      regret (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values b
        (poorLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) b)
        (richLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k))≤
          3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32+2/((prepare m k).K:ℝ)+(m:ℝ)/(prepare m k).S := by
  rw [GeneralPaperCheckedSourcePair.run_eq k Qv hm hQv weights hp hs b hb]
  exact GeneralPaperSourcePairCanonical.run_regrets k Qv hm hQv weights hp hs b hb

theorem dyadic_run_regrets {m : ℕ} (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1)
    (Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) :
    let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
    ∃ pair,run k Qv hQv weights hp hs b=some pair ∧ GeneralPaperSourcePairContract.Contract k Qv hQv weights hp hs b pair ∧
      Supported 1 (richLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)) ∧
      Supported b (poorLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) b) ∧
      regret (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values 1
        (richLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k))
        (poorLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) b)≤(epsilon:ℝ)/16 ∧
      regret (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values b
        (poorLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) b)
        (richLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k))≤(epsilon:ℝ)/16 := by
  dsimp only
  rw [GeneralPaperCheckedSourcePair.run_eq (GeneralPaperDyadicAccuracy.prepare epsilon).exponent Qv hm hQv weights hp hs b hb]
  exact GeneralPaperSourceDyadicEquilibrium.run_regrets epsilon hE hOne Qv hm hQv weights hp hs b hb

end Blotto.GeneralPaperCheckedSourceEquilibrium
