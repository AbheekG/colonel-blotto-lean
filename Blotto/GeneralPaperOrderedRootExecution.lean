import Blotto.GeneralPaperTypedDecodePrice

/-! Execute the DP once, select a root label once and follow the retained
computation once. The full native Option result agrees, including every
failure branch and all returned typed option indices. -/
namespace Blotto.GeneralPaperOrderedRootExecution
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run {K q w B h : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h) (budget : Tag) :
    Option (Fin grid.size × List (Fin K)) × ℕ :=
  let computed := GeneralPaperOrderedDPExecution.run bits index price W grid tree
  let selected := GeneralPaperRootSelectPrice.run bits index price W computed.1.table budget
  let A := if bits then arrayWord W (max K grid.size+2) else W
  match selected.1 with
  | none => (none,computed.2+selected.2+128*W)
  | some label =>
    let decoded := GeneralPaperTypedDecodeExecution.run A computed.1 label
    (decoded.1.map (fun labels => (label,labels)),computed.2+selected.2+decoded.2+128*W)

theorem data {K q w B h : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h) (budget : Tag) :
    (run bits index price W grid tree budget).1=GeneralPaperOrderedProfitRoot.solve grid tree budget := by
  simp only [run,GeneralPaperRootSelectPrice.data,GeneralPaperOrderedDPExecution.data,
    GeneralPaperTypedDecodeExecution.data,GeneralPaperOrderedProfitRoot.solve]
  cases hSelected : GeneralPaperOrderedProfitRoot.select (GeneralPaperOrderedProfitDP.run grid tree).table budget <;> rfl

end Blotto.GeneralPaperOrderedRootExecution
