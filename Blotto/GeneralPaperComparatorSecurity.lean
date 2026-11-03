import Blotto.GeneralPaperRationalComparator
import Blotto.GeneralPaperComparatorParameters
import Blotto.ContinuousSecurityValues

/-! The paper's near-optimal finite code comparator, with its actual
K_c=64/z error. Real joint weights are retained and every row is feasible.
The comparator is an existence argument, not an algorithmic input.
-/
namespace Blotto.GeneralPaperComparatorSecurity
open GeneralPaperCodeAlphabet GeneralPaperCodeMixturePhysical ContinuousSecurityValues
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem near_optimal {m : ℕ} (a : Alphabet) (k : ℕ) (v : Values m)
    (budgets : Fin 2 → ℚ) (own opposing : Fin 2)
    (hOwn : 0≤(budgets own:ℝ) ∧ (budgets own:ℝ)≤1) (hOpposing : 0≤(budgets opposing:ℝ))
    (hD : RationalOrderCell.commonDenominator budgets*(m+2)^
      (m*((GeneralPaperComparatorParameters.countRun k).power-1)+1)≤a.D) (qbar : ℕ) :
    ∃ X : GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a false (budgets own),
      security v (budgets opposing:ℝ) (physicalLaw X qbar)<
        lossInfimum v (budgets own:ℝ) (budgets opposing:ℝ)+((GeneralPaperSourceParameters.prepare k).z:ℝ)/32 := by
  have hz : 0<((GeneralPaperSourceParameters.prepare k).z:ℝ)/64 := by
    have hp : (0:ℝ)<(GeneralPaperSourceParameters.prepare k).z :=
      by exact_mod_cast (GeneralPaperSourceParameters.positive k).1
    positivity
  obtain ⟨law,hLaw,hNear⟩ := exists_near_optimal v (budgets own:ℝ) (budgets opposing:ℝ)
    hOwn.1 hOpposing _ hz
  obtain ⟨X,hCompare,hFinite⟩ := GeneralPaperRationalComparator.exists_code_comparator a v law budgets own opposing
    hOwn.2 hLaw hOpposing (GeneralPaperComparatorParameters.countRun k).power
    (GeneralPaperComparatorParameters.count_positive k) hD qbar
  rw [GeneralPaperComparatorParameters.count_error] at hCompare
  exact ⟨X,by linarith⟩

end Blotto.GeneralPaperComparatorSecurity
