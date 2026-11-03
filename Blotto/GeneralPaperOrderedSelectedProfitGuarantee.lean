import Blotto.GeneralPaperProfitParameters
import Blotto.GeneralPaperOrderedProfitApproximation

/-! The selected, actually prepared fixed-grid optimizer achieves the
paper's alpha/2 error at the source accuracy eta=alpha. Input profit/domain
and physical resource/catalogue correspondence still require their source
construction; no optimizer-accuracy assumption is supplied here.
-/
namespace Blotto.GeneralPaperOrderedSelectedProfitGuarantee
open GeneralPaperOrderedProfitDP GeneralPaperOrderedProfitSound GeneralPaperOrderedProfitTreeBounds GeneralPaperProfitRationalRound
open GeneralPaperProfitParameters
set_option autoImplicit false
variable {R : Type} [LinearOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R]
set_option maxHeartbeats 3500000

def solve {K : ℕ} (prepared : GeneralPaperProfitParameters.Prepared)
    (tree : Tree R K prepared.parameters.height) (budget : R) :
    Option (Fin prepared.grid.size × List (Fin K)) :=
  GeneralPaperOrderedProfitRoot.solve prepared.grid tree budget

theorem selected_guarantee {K : ℕ} (m lambda k Qv : ℕ) (hQv : 0<Qv)
    (tree : Tree R K (parameters m lambda k Qv).height) (budget : R)
    (hBound : BoundedProfit (parameters m lambda k Qv).qProf tree)
    (labels : List (Fin K)) (cost : R) (P : ℕ) (hRealizes : Realizes tree labels cost P) (hBudget : cost≤budget) :
    ∃ label output outCost outProfit,
      solve (prepare m lambda k Qv) tree budget=some (label,output) ∧
      Realizes tree output outCost outProfit ∧ outCost≤budget ∧
      profit (parameters m lambda k Qv).qProf P-profit (parameters m lambda k Qv).qProf outProfit≤
        (GeneralPaperSourceParameters.prepare k).eta/2 := by
  exact GeneralPaperOrderedProfitApproximation.optimizer_guarantee tree budget (GeneralPaperSourceParameters.prepare k).eta
    (qProf_positive m lambda k Qv hQv) (width_lower m lambda k Qv) (exponent_lower m lambda k Qv)
    hBound (accuracy m lambda k Qv) labels cost P hRealizes hBudget

end Blotto.GeneralPaperOrderedSelectedProfitGuarantee
