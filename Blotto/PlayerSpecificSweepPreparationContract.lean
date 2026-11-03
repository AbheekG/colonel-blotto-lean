import Blotto.PlayerSpecificSweepPreparationCopyCost

/-! Actual one-time rational sweep preparation has complete source time,
all returned-cell size bounds and a polynomial schoolbook cost. Sorting the
field row and final recognition/description joins remain separate callers. -/
namespace Blotto.PlayerSpecificSweepPreparationContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificRationalSweepHeights PlayerSpecificRationalTrace
open PlayerSpecificSweepPreparationBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem total_profile (N R initial suffix cells frame : ℕ)
    (hi : initial≤300*(N+1)^2*R) (hs : suffix≤300*(N+1)^2*R)
    (hc : cells≤10000*(N+2)^2*R) (hf : frame≤1000*(N+2)*R) :
    initial+suffix+cells+frame≤20000*(N+2)^2*R := by
  have hnR : 0≤N*R := Nat.zero_le _
  have hn2R : 0≤N^2*R := Nat.zero_le _
  nlinarith only [hi,hs,hc,hf,hnR,hn2R]

theorem source_cost (model : RationalCostModel) (fields : List (ℚ×ℚ)) (H : ℕ)
    (hf : FieldsHeight fields H) (hH : 1≤H) :
    (PlayerSpecificSweepPreparationExecution.run model fields).2≤20000*(fields.length+2)^2*model.rat (width fields.length H) := by
  have hp:=profiles fields.length H
  have hi:=PlayerSpecificSweepInitialCost.source_cost model fields fields.length H hf (le_refl _) hH
  have hip:=hi.trans (Nat.mul_le_mul_left _ (model.monotone hp.2.2.1))
  have hs:=PlayerSpecificSuffixCost.source_cost model fields fields.length H hf (le_refl _) hH
  have hsp:=hs.trans (Nat.mul_le_mul_left _ (model.monotone hp.2.2.2.1))
  have hh:=PlayerSpecificSweepTraceFits.initial_height fields fields.length H hf (le_refl _) hH
  have hxs:=(PlayerSpecificSuffixCost.returned_heights fields H hf hH).2
  have hc:=PlayerSpecificCellConstructionCost.source_cost model (PlayerSpecificSweepExecution.initial fields).1 0
    (PlayerSpecificSuffixExecution.run fields).1.2 (initialBound fields.length H) H hh
    (zero_height.mono (by unfold initialBound; omega)) hxs
  rw [PlayerSpecificSuffixExecution.rows_length] at hc
  have hcp:=hc.trans (Nat.mul_le_mul_left _ (model.monotone hp.2.2.2.2.1))
  have hframe:=PlayerSpecificSweepPreparationCopyCost.frame_cost model fields H hf hH
  simp only [PlayerSpecificSweepPreparationExecution.run] at hframe ⊢
  exact total_profile fields.length _ _ _ _ _ hip hsp hcp hframe

theorem actual_contract (model : RationalCostModel) (fields : List (ℚ×ℚ)) (H : ℕ)
    (hf : FieldsHeight fields H) (hH : 1≤H) :
    let result:=PlayerSpecificSweepPreparationExecution.run model fields
    result.1=build (PlayerSpecificSweep.initial fields) 0 (PlayerSpecificSweepBounds.suffixes fields).2.1 ∧
      result.1.length=fields.length+1 ∧ (∀ c∈result.1,CellHeight c (height fields.length H)) ∧
      result.2≤20000*(fields.length+2)^2*model.rat (width fields.length H) :=
  ⟨PlayerSpecificSweepPreparationExecution.value model fields,PlayerSpecificSweepPreparationExecution.count model fields,
    PlayerSpecificSweepPreparationCopyCost.cell_heights model fields H hf hH,source_cost model fields H hf hH⟩

end Blotto.PlayerSpecificSweepPreparationContract
