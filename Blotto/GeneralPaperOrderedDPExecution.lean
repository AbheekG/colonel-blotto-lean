import Blotto.GeneralPaperOrderedTableArithmetic

/-! Full recursive native DP computation. Each child is computed once and
retained with the merged table for backtracking. Height/price projections
are analysis only; the execution performs no validity or metadata scan. -/
namespace Blotto.GeneralPaperOrderedDPExecution
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedProfitDP
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run {K q w B : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) : {h : ℕ} → Tree Tag K h → Computation Tag K grid.size h × ℕ
  | _,.leaf field =>
    let states := GeneralPaperOrderedTableExecution.leaf bits index price W grid field
    (.leaf states.1,states.2+128*W)
  | _,.node left right =>
    let lc := run bits index price W grid left
    let rc := run bits index price W grid right
    let states := GeneralPaperOrderedTableExecution.merge bits index price W grid lc.1.table rc.1.table
    (.node lc.1 rc.1 states.1,lc.2+rc.2+states.2+128*W)

theorem data {K q w B h : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h) :
    (run bits index price W grid tree).1=GeneralPaperOrderedProfitDP.run grid tree := by
  induction tree with
  | leaf field => simp only [run,GeneralPaperOrderedTableExecution.leaf_data,GeneralPaperOrderedProfitDP.run]
  | node left right ihl ihr =>
    simp only [run,ihl,ihr,GeneralPaperOrderedTableExecution.merge_data,GeneralPaperOrderedProfitDP.run]

theorem states {K q w B h : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W s : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h) (hl : GeneralPaperOrderedDPHeight.Leaves s tree) :
    GeneralPaperOrderedTableHeight.Safe (expressionHeightBudget s h) (run bits index price W grid tree).1.table := by
  rw [data]
  exact GeneralPaperOrderedDPHeight.states grid tree s hl

end Blotto.GeneralPaperOrderedDPExecution
