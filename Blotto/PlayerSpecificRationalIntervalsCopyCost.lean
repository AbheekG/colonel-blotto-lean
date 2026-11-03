import Blotto.PlayerSpecificRationalIntervalsExecution

/-! All original/cached/returned records in complete interval preparation
have polynomial source-copy cost derived from the original encoded input. -/
namespace Blotto.PlayerSpecificRationalIntervalsCopyCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def inputSize {N : ℕ} (i : RationalPlayerSpecificInput N) : ℕ := PlayerSpecificRecognitionInputHeights.inputHeight i
def height (N L : ℕ) : ℕ := PlayerSpecificSweepPreparationBudget.height N L
def width (N L : ℕ) : ℕ := PlayerSpecificSweepPreparationBudget.width N L

theorem widths (N L : ℕ) : PlayerSpecificBitRatioSortBudget.width N L≤width N L ∧
    128*(height N L+1)≤width N L ∧ 2*N+3≤width N L ∧ 1+2*L≤width N L := by
  have hp:=PlayerSpecificSweepPreparationBudget.profiles N L
  have hNL : 0≤N*L := Nat.zero_le _
  refine ⟨?_,hp.2.2.2.2.2.1,?_,?_⟩ <;>
    dsimp only [PlayerSpecificBitRatioSortBudget.width,width,PlayerSpecificSweepPreparationBudget.width] <;>
    nlinarith only [hNL]

theorem row_length {N : ℕ} (i : RationalPlayerSpecificInput N) : (PlayerSpecificRecognitionInputHeights.row i).length=2*N+1 := by
  simp only [PlayerSpecificRecognitionInputHeights.row,List.length_cons,List.length_append,List.length_ofFn]
  omega

theorem frame_cost {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    price model (PlayerSpecificRationalIntervalsExecution.frame i (PlayerSpecificSortedFieldsExecution.run model i).1
      (PlayerSpecificRationalIntervalsExecution.run model i).1)≤1000*(N+2)*model.rat (width N (inputSize i)) := by
  let L:=inputSize i
  let W:=width N L
  have hp:=widths N L
  have hW : 6≤W := by unfold W width PlayerSpecificSweepPreparationBudget.width; nlinarith
  have hinput:=price_bound model W (by omega) _ (copyRow_fits W (PlayerSpecificRecognitionInputHeights.row i)
    (fun q hq => (rationalWordWidth_of_height (input_height (PlayerSpecificRecognitionInputHeights.row i) q hq)).trans hp.2.2.2)
    (by rw [row_length]; dsimp only [W]; omega))
  rw [copyRow_length,row_length] at hinput
  have hfieldsHeight:=PlayerSpecificSortedFieldsExecution.heights model i
  have hfieldsLen:=PlayerSpecificSortedFieldsExecution.length model i
  have hfields:=price_bound model W (by omega) _
    (PlayerSpecificSweepTraceFits.copy_fields_fits (PlayerSpecificSortedFieldsExecution.run model i).1 L W hfieldsHeight
      hp.2.2.2 (by rw [hfieldsLen]; dsimp only [W]; omega) (by omega))
  rw [PlayerSpecificSweepExecution.copy_fields_length,hfieldsLen] at hfields
  have hcellsHeight:=PlayerSpecificRationalIntervalsExecution.heights model i
  have hcellsLen:=PlayerSpecificRationalIntervalsExecution.length model i
  have hcells:=PlayerSpecificCellConstructionCopyCost.cells_copy model (PlayerSpecificRationalIntervalsExecution.run model i).1
    (height N L) W hcellsHeight hp.2.1 (by rw [hcellsLen]; dsimp only [W]; omega)
  rw [hcellsLen] at hcells
  have hctrl : Fits W [.control N,.control (PlayerSpecificRationalIntervalsExecution.run model i).1.length] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · exact (PlayerSpecificRationalTrace.control_width _).trans (by dsimp only [W]; omega)
    · exact (PlayerSpecificRationalTrace.control_width _).trans (by rw [hcellsLen]; dsimp only [W]; omega)
  have hcontrols:=price_bound model W (by omega) _ hctrl
  simp only [List.length_cons,List.length_nil] at hcontrols
  simp only [PlayerSpecificRationalIntervalsExecution.frame,price_append]
  nlinarith only [hinput,hfields,hcells,hcontrols]

end Blotto.PlayerSpecificRationalIntervalsCopyCost
