import Blotto.PlayerSpecificCellConstructionCopyCost

/-! Complete source time for literal rational cell construction. Additive
sweep heights give one polynomial width over the whole recursion; every
ratio/move, suffix-input list and returned-cell list is priced. -/
namespace Blotto.PlayerSpecificCellConstructionCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificRationalSweepHeights PlayerSpecificSweep PlayerSpecificRationalTrace
open PlayerSpecificCellConstructionCopyCost
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem height_step (T H N : ℕ) : height (stepBound T H) H N=height T H (N+1) := by
  unfold height bound stepBound
  ring
theorem child_width (T H N : ℕ) : width (stepBound T H) H N≤width T H (N+1) := by
  unfold width
  rw [height_step]
  unfold PlayerSpecificSweepTraceFits.width
  omega

theorem price_profile (n R ratio moved child frame : ℕ) (hr : ratio≤15*R) (hm : moved≤180*R)
    (hc : child≤10000*(n+2)^2*R) (hf : frame≤500*((n+1)+2)*R) :
    ratio+moved+child+frame≤10000*((n+1)+2)^2*R := by
  have hnr : 0≤n*R := Nat.zero_le _
  nlinarith only [hr,hm,hc,hf,hnr]

theorem source_cost (model : RationalCostModel) (s : State ℚ) (lower : ℚ) (xs : PlayerSpecificSuffixExecution.Rows)
    (T H : ℕ) (hs : StateHeight s T) (hl : RationalHeight lower T) (hx : PlayerSpecificSuffixCost.RowsHeight xs H) :
    (PlayerSpecificCellConstructionExecution.run model s lower xs).2≤
      10000*(xs.length+2)^2*model.rat (width T H xs.length) := by
  induction xs generalizing s lower T with
  | nil =>
    have hf:=frame_cost model s lower [] T H hs hl hx
    simp only [PlayerSpecificCellConstructionExecution.run,List.length_nil,Nat.zero_add]
    exact hf.trans (Nat.mul_le_mul_right _ (by decide : 500*(0+2)≤10000*(0+2)^2))
  | cons x xs ih =>
    have hhead:=hx x List.mem_cons_self
    have htail : PlayerSpecificSuffixCost.RowsHeight xs H := fun y hy => hx y (List.mem_cons_of_mem x hy)
    have hstate : StateHeight (PlayerSpecificSweepExecution.move s x.1.1 x.1.2).1 (stepBound T H) := by
      rw [PlayerSpecificSweepExecution.move_value]
      exact move_height s x.1.1 x.1.2 T H hs hhead.1 hhead.2.1
    have hratio : RationalHeight (scalar .divide x.1.1 x.1.2).1 (stepBound T H) := by
      simpa only [scalar_value,Arithmetic.apply] using (hhead.1.div hhead.2.1).mono (show H+H≤stepBound T H by unfold stepBound; omega)
    have ht:=ih (PlayerSpecificSweepExecution.move s x.1.1 x.1.2).1
      (scalar .divide x.1.1 x.1.2).1 (stepBound T H) hstate hratio htail
    have htp:=ht.trans (Nat.mul_le_mul_left _ (model.monotone (child_width T H xs.length)))
    have hw:=large T H (x::xs).length
    have hrfit:=fits_mono (scalar_fits_height .divide x.1.1 x.1.2 (height T H (x::xs).length)
      (hhead.1.mono hw.2.1) (hhead.2.1.mono hw.2.1)) (show
        4*height T H (x::xs).length+3≤width T H (x::xs).length by
        unfold width PlayerSpecificSweepTraceFits.width
        omega)
    have hr:=price_bound model (width T H (x::xs).length) (by have hh:=hw.2.2.2.2; omega) _ hrfit
    rw [scalar_length] at hr
    have hm:=PlayerSpecificSweepMoveCost.source_cost model s x.1.1 x.1.2 T H hs hhead.1 hhead.2.1
    have hmWidth : PlayerSpecificSweepTraceFits.width (stepBound T H) 0≤width T H (x::xs).length := by
      change 128*(stepBound T H+0+1)≤128*(height T H (x::xs).length+((x::xs).length+2)+1)
      omega
    have hmp:=hm.trans (Nat.mul_le_mul_left 180 (model.monotone hmWidth))
    have hf:=frame_cost model s lower (x::xs) T H hs hl hx
    simp only [PlayerSpecificCellConstructionExecution.run] at hf ⊢
    simpa only [List.length_cons] using price_profile xs.length _ _ _ _ _ hr hmp htp hf

theorem actual_contract (model : RationalCostModel) (s : State ℚ) (lower : ℚ) (xs : PlayerSpecificSuffixExecution.Rows)
    (T H : ℕ) (hs : StateHeight s T) (hl : RationalHeight lower T) (hx : PlayerSpecificSuffixCost.RowsHeight xs H) :
    let result:=PlayerSpecificCellConstructionExecution.run model s lower xs
    result.1=build s lower xs ∧ result.1.length=xs.length+1 ∧
      (∀ c∈result.1,CellHeight c (height T H xs.length)) ∧
      result.2≤10000*(xs.length+2)^2*model.rat (width T H xs.length) := by
  refine ⟨PlayerSpecificCellConstructionExecution.value model s lower xs,
    PlayerSpecificCellConstructionExecution.length model s lower xs,?_,source_cost model s lower xs T H hs hl hx⟩
  rw [PlayerSpecificCellConstructionExecution.value]
  exact build_height s lower xs T H hs hl hx

end Blotto.PlayerSpecificCellConstructionCost
