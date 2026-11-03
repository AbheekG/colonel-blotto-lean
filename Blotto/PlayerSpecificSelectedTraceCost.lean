import Blotto.PlayerSpecificSelectedSizeBudget

/-! Complete per-frame and per-split source prices for a selected root.
All cached rows, current/returned records and branch controls are included. -/
namespace Blotto.PlayerSpecificSelectedTraceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificIsolationState PlayerSpecificRationalTrace
open PlayerSpecificSignPreparationBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem frame_cost (model : RationalCostModel) (m a : Data) (original : Interval) (prepared : Prepared m)
    (hml : m.length≤4) (fuel : ℕ) (node result : Interval)
    (hn : Valid prepared node) (hr : Valid prepared result)
    (hnlo : RationalHeight node.lo (height (PlayerSpecificSignLinearSizes.inputHeight m a original)))
    (hnhi : RationalHeight node.hi (height (PlayerSpecificSignLinearSizes.inputHeight m a original)))
    (hrlo : RationalHeight result.lo (height (PlayerSpecificSignLinearSizes.inputHeight m a original)))
    (hrhi : RationalHeight result.hi (height (PlayerSpecificSignLinearSizes.inputHeight m a original)))
    (hf : fuel≤height (PlayerSpecificSignLinearSizes.inputHeight m a original)) :
    price model (PlayerSpecificSelectedExecution.frame prepared fuel node result)≤
      150*model.rat (width (PlayerSpecificSignLinearSizes.inputHeight m a original)) := by
  let H:=PlayerSpecificSignLinearSizes.inputHeight m a original
  change fuel≤height H at hf
  have hw:=copy_width H
  have hrows:=PlayerSpecificSelectedSizeBudget.rows m a original prepared hml
  have hrowprice:=PlayerSpecificSturmCopyCost.copyRows_cost model _ (height H) (width H) hrows.2 hrows.1 hw.1 hw.2
  have hnc:=PlayerSpecificSplitExecution.stored_counts m prepared hml node hn
  have hrc:=PlayerSpecificSplitExecution.stored_counts m prepared hml result hr
  have hnp:=PlayerSpecificSplitTraceCost.copyInterval_cost model node (height H) (width H) hnlo hnhi hnc.1 hnc.2.1 hw.1 (by omega)
  have hrp:=PlayerSpecificSplitTraceCost.copyInterval_cost model result (height H) (width H) hrlo hrhi hrc.1 hrc.2.1 hw.1 (by omega)
  have hctrl : Fits (width H) [.control fuel,.control node.count,.control 1] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl <;> exact (PlayerSpecificRationalTrace.control_width _).trans (by unfold width; omega)
  have hp:=price_bound model (width H) (by omega) _ hctrl
  simp only [List.length_cons,List.length_nil] at hp
  simp only [PlayerSpecificSelectedExecution.frame,price_append]
  nlinarith only [hrowprice,hnp,hrp,hp]

theorem split_cost (model : RationalCostModel) (m a : Data) (original : Interval) (prepared : Prepared m)
    (hml : m.length≤4) (node : Interval) (hn : Valid prepared node)
    (hlo : RationalHeight node.lo (height (PlayerSpecificSignLinearSizes.inputHeight m a original)))
    (hhi : RationalHeight node.hi (height (PlayerSpecificSignLinearSizes.inputHeight m a original))) :
    price model (PlayerSpecificSplitExecution.run prepared node).2≤
      5000*model.rat (width (PlayerSpecificSignLinearSizes.inputHeight m a original)) :=
  (PlayerSpecificSplitTraceCost.run_cost model m prepared hml node hn _ hlo hhi).trans
    (Nat.mul_le_mul_left 5000 (model.monotone (PlayerSpecificSelectedSizeBudget.split_width m a original hml)))

end Blotto.PlayerSpecificSelectedTraceCost
