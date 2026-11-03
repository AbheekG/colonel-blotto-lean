import Blotto.PlayerSpecificFiniteParameterBudget

/-! Proof-only views of the caller's once-computed preparation, selection
and accepted scale. Public runtime code executes each stage directly and
does not call these views or receive their bounds as inputs. -/
namespace Blotto.PlayerSpecificFiniteParameterStages
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificFiniteParameterBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

def prepared {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :=
  PlayerSpecificRationalIntervalsExecution.run model i
def selected {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :=
  PlayerSpecificRecognitionScanExecution.run model i.budget (prepared model i).1
def scale {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N)
    (chosen : PlayerSpecificRationalCells.Cell×PlayerSpecificAlgebraicCandidates.Candidate) :=
  PlayerSpecificFiniteScaleExecution.run model chosen.1 i.budget chosen.2.polynomial

theorem selected_value {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    (selected model i).1=PlayerSpecificFiniteRecognition.run model i := by
  simp only [selected,prepared,PlayerSpecificRationalIntervalsExecution.value,
    PlayerSpecificRecognitionScanExecution.value model i.budget i.budget_pos.ne',PlayerSpecificFiniteRecognition.run]

theorem preparation_cost {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    (prepared model i).2≤10000000*work N (inputSize i)*model.rat (width N (inputSize i)) := by
  have hc:=PlayerSpecificRationalIntervalsContract.source_cost model i
  have hw:=Nat.mul_le_mul_left 10000000 (work_profiles N (inputSize i)).1
  exact hc.trans (Nat.mul_le_mul hw (model.monotone (preparation_width N (inputSize i))))

theorem scan_cost {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    (selected model i).2≤PlayerSpecificRecognitionScanContract.workCoefficient*work N (inputSize i)*
      model.rat (width N (inputSize i)) := by
  have hc:=PlayerSpecificRecognitionScanContract.source_cost model i
  have hw:=Nat.mul_le_mul_left PlayerSpecificRecognitionScanContract.workCoefficient (work_profiles N (inputSize i)).2.1
  have hprofile : PlayerSpecificRecognitionScanContract.workCoefficient*(N+1)^2*(inputSize i+1)*
      model.rat (PlayerSpecificRecognitionScanContract.widthCoefficient*((N+1)*(inputSize i+1)))≤
      PlayerSpecificRecognitionScanContract.workCoefficient*work N (inputSize i)*model.rat (width N (inputSize i)) := by
    simpa only [mul_assoc] using Nat.mul_le_mul hw (model.monotone (scan_width N (inputSize i)))
  have hp:=hc.trans hprofile
  simpa only [selected,prepared,PlayerSpecificRationalIntervalsExecution.value] using hp

theorem accepted_scale {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N)
    (chosen : PlayerSpecificRationalCells.Cell×PlayerSpecificAlgebraicCandidates.Candidate)
    (hr : (selected model i).1=some chosen) :
    HasHeight (scale model i chosen).1 (height N (inputSize i)) ∧ (scale model i chosen).1.length≤3 ∧
      (scale model i chosen).2≤1000000000*model.rat (width N (inputSize i)) := by
  have hold : PlayerSpecificFiniteRecognition.run model i=some chosen := (selected_value model i).symm.trans hr
  have hs:=PlayerSpecificFiniteParameterSizes.recognition_return model i chosen.1 chosen.2 hold
  have hgood:=(PlayerSpecificFiniteRecognition.sound model i chosen.1 chosen.2 hold).1
  have hm0 : chosen.2.polynomial≠[] := by intro hz; exact hgood.2.1.ne_zero (by rw [hz]; rfl)
  have hb : RationalHeight i.budget (cellHeight N (inputSize i)) :=
    (PlayerSpecificRecognitionInputHeights.original_fields i).1.mono
      ((Nat.le_succ (inputSize i)).trans (PlayerSpecificFiniteParameterSizes.cell_large N (inputSize i)))
  have hc:=PlayerSpecificFiniteScaleContract.actual_contract model chosen.1 i.budget chosen.2.polynomial
    (cellHeight N (inputSize i)) hs.1 hb hgood.1 hm0 hgood.2.2.1 hs.2.1
  exact ⟨hc.2.2.2.1,hc.2.2.1,hc.2.2.2.2.trans
    (Nat.mul_le_mul_left 1000000000 (model.monotone (scale_width N (inputSize i))))⟩

end Blotto.PlayerSpecificFiniteParameterStages
