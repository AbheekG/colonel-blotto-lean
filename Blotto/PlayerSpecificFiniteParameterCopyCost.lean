import Blotto.PlayerSpecificFiniteParameterStages

/-! Complete original-input and accepted-output copy prices for the final
recognizer. Selected root/cell copies come from the actual scan handover;
the retained scale uses its proved computed height and three-entry bound. -/
namespace Blotto.PlayerSpecificFiniteParameterCopyCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificFiniteParameterBudget PlayerSpecificFiniteParameterStages PlayerSpecificFiniteParameterExecution
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem input_copy {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    price model (copyRow (PlayerSpecificRecognitionInputHeights.row i))≤6*(N+1)*model.rat (width N (inputSize i)) := by
  have hw:=output_width N (inputSize i)
  have hword : 1+2*inputSize i≤width N (inputSize i) :=
    (PlayerSpecificRationalIntervalsCopyCost.widths N (inputSize i)).2.2.2.trans (preparation_width N (inputSize i))
  have hp:=price_bound model (width N (inputSize i)) (by omega) _ (copyRow_fits _ _
    (fun q hq => (rationalWordWidth_of_height (input_height (PlayerSpecificRecognitionInputHeights.row i) q hq)).trans hword)
    (by rw [PlayerSpecificRationalIntervalsCopyCost.row_length]; omega))
  rw [copyRow_length,PlayerSpecificRationalIntervalsCopyCost.row_length] at hp
  nlinarith only [hp]

theorem controls {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N)
    (result : Option PlayerSpecificFiniteParameterReturn.Result) :
    price model [.control N,.control (if result.isSome then 1 else 0)]≤6*model.rat (width N (inputSize i)) := by
  have hw:=output_width N (inputSize i)
  have hf : Fits (width N (inputSize i)) [.control N,.control (if result.isSome then 1 else 0)] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · exact (PlayerSpecificRationalTrace.control_width _).trans (by omega)
    · exact (PlayerSpecificRationalTrace.control_width _).trans (by split <;> omega)
  exact price_bound model _ (by omega) _ hf

theorem none_frame {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    price model (frame i none)≤1000*work N (inputSize i)*model.rat (width N (inputSize i)) := by
  have hi:=input_copy model i
  have hc:=controls model i none
  have hw:=output_width N (inputSize i)
  have hn:=event_price model (width N (inputSize i)) (by omega) (.control 0) ((PlayerSpecificRationalTrace.control_width 0).trans (by omega))
  change price model [.control 0]≤3*model.rat (width N (inputSize i)) at hn
  have hm:=Nat.mul_le_mul_right (1000*model.rat (width N (inputSize i))) (work_profiles N (inputSize i)).2.2.1
  simp only [frame,copyResult,price_append]
  nlinarith only [hi,hc,hn,hm]

theorem accepted_frame {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N)
    (chosen : PlayerSpecificRationalCells.Cell×PlayerSpecificAlgebraicCandidates.Candidate)
    (hr : (selected model i).1=some chosen) :
    price model (frame i (some ⟨chosen.1,chosen.2,(scale model i chosen).1⟩))≤
      (selected model i).2+1000*work N (inputSize i)*model.rat (width N (inputSize i)) := by
  have hs:=accepted_scale model i chosen hr
  have hw:=output_width N (inputSize i)
  have hscale:=PlayerSpecificExtendedCopyCost.row_cost model (scale model i chosen).1 (height N (inputSize i))
    (width N (inputSize i)) hs.1 (by omega) hw.1 hw.2.2
  have hselected:=PlayerSpecificRecognitionScanHandover.returned_copy_le model i.budget (prepared model i).1
  change price model (PlayerSpecificRecognitionScanExecution.copyResult (selected model i).1)≤(selected model i).2 at hselected
  rw [hr] at hselected
  simp only [PlayerSpecificRecognitionScanExecution.copyResult,price_append] at hselected
  have hi:=input_copy model i
  have hc:=controls model i (some ⟨chosen.1,chosen.2,(scale model i chosen).1⟩)
  have hm:=Nat.mul_le_mul_right (1000*model.rat (width N (inputSize i))) (work_profiles N (inputSize i)).2.2.1
  simp only [frame,copyResult,price_append]
  nlinarith only [hscale,hselected,hi,hc,hm]

end Blotto.PlayerSpecificFiniteParameterCopyCost
