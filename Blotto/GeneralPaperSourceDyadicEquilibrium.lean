import Blotto.GeneralPaperReducedErrorBudget
import Blotto.GeneralPaperDyadicAccuracy

/-! The ACTUAL rational accuracy input selects k and the actual source,
classifier, original-basis transfer and decoded whole-row pair return a
canonical continuous-game approximate Nash pair at budgets 1 and b.
This is the normalized integer-value reduced game, before value reduction,
circle lifting, output sampling and complete paper computational prices.
-/
namespace Blotto.GeneralPaperSourceDyadicEquilibrium
open GeneralPaperProxyParameters GeneralPaperSourcePairRun GeneralPaperSourcePairCanonical
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem selected_accuracy (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1) :
    (GeneralPaperReducedErrorBudget.accuracy (GeneralPaperDyadicAccuracy.prepare epsilon).exponent:ℝ)≤(epsilon:ℝ) := by
  have hh := (GeneralPaperDyadicAccuracy.accuracy_bounds epsilon hE hOne).2
  rw [GeneralPaperDyadicAccuracy.accuracy_power] at hh
  unfold GeneralPaperReducedErrorBudget.accuracy
  exact_mod_cast hh

theorem run_regrets {m : ℕ} (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1)
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
  let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
  obtain ⟨pair,hRun,hc,hA,hB,hRA,hRB⟩ := GeneralPaperSourcePairCanonical.run_regrets k Qv hm hQv weights hp hs b hb
  have hg := GeneralPaperReducedErrorBudget.real_gap m k hm
  have he := div_le_div_of_nonneg_right (selected_accuracy epsilon hE hOne) (by norm_num : (0:ℝ)≤16)
  exact ⟨pair,hRun,hc,hA,hB,hRA.trans (hg.le.trans he),hRB.trans (hg.le.trans he)⟩

end Blotto.GeneralPaperSourceDyadicEquilibrium
