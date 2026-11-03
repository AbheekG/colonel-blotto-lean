import Blotto.PlayerSpecificAlgebraicInitialVectorBudget

/-! Proof-only views and source bounds for the actual cached vector
stages. The executing routine retains each stage once and does not call
these views. -/
namespace Blotto.PlayerSpecificAlgebraicInitialVectorStages
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicInitialVectorBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

def first {N : ℕ} (i : RationalPlayerSpecificInput N) := PlayerSpecificInputArrayExecution.run RationalCostModel.schoolbook i.valuesA.weight
def second {N : ℕ} (i : RationalPlayerSpecificInput N) := PlayerSpecificInputArrayExecution.run RationalCostModel.schoolbook i.valuesB.weight
def inverse (r : PlayerSpecificFiniteParameterReturn.Result) :=
  PlayerSpecificAlgebraicInverseExecution.run RationalCostModel.schoolbook r.root.polynomial r.scale
def rows {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) :=
  PaperIndexedArrayConstruction.run RationalCostModel.schoolbook.rat (address N)
    (PlayerSpecificAlgebraicInitialVectorExecution.callback RationalCostModel.schoolbook (address N) r.root (inverse r).1 (first i).1 (second i).1)

theorem callback_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) (j : Fin N) :
    (PlayerSpecificAlgebraicInitialVectorExecution.callback RationalCostModel.schoolbook (address N) r.root
      (inverse r).1 (first i).1 (second i).1 j).2≤callbackCoefficient*size N (inputSize i)*RationalCostModel.schoolbook.rat (width N (inputSize i)) := by
  have hc:=PlayerSpecificAlgebraicInitialOriginalCost.source_cost i r hr j
  have hm:=Nat.mul_le_mul_left (PlayerSpecificAlgebraicInitialOriginalCost.workCoefficient*size N (inputSize i))
    (RationalCostModel.schoolbook.monotone (field_width N (inputSize i)))
  have hi:=hc.trans hm
  have hweights:=PlayerSpecificRecognitionInputHeights.original_fields i
  have hCW:=copy_width N (inputSize i)
  have hrow:=cons_height ((hweights.2.1 j).mono (input_le_height N (inputSize i)))
    (cons_height ((hweights.2.2 j).mono (input_le_height N (inputSize i))) (nil_height _))
  have hcopy:=PlayerSpecificExtendedCopyCost.row_cost RationalCostModel.schoolbook [i.valuesA.weight j,i.valuesB.weight j]
    (PlayerSpecificAlgebraicInitialInputSizes.height N (inputSize i)) (width N (inputSize i)) hrow (by simp) hCW.1 hCW.2.1
  have haddr:=(address_bounds N (inputSize i)).2.1
  have hu:=Nat.mul_le_mul_right (RationalCostModel.schoolbook.rat (width N (inputSize i))) (size_bounds N (inputSize i)).1
  simp only [PlayerSpecificAlgebraicInitialVectorExecution.callback,first,second,inverse,
    PlayerSpecificInputArrayExecution.value,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicInverseExecution.value]
  dsimp only [PlayerSpecificAlgebraicInitialOriginalCost.fieldCall,PlayerSpecificAlgebraicInitialVector.prepare] at hi
  unfold callbackCoefficient
  nlinarith only [hi,hcopy,haddr,hu]

theorem rows_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    (rows i r).2≤N*(callbackCoefficient*size N (inputSize i)*RationalCostModel.schoolbook.rat (width N (inputSize i)))+
      44*(N+1)*address N :=
  GeneralPaperControlArrayPrice.indexed_work _ _ _ _ (address_bounds N (inputSize i)).1
    (address_bounds N (inputSize i)).2.2 (callback_cost i r hr)

theorem inverse_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    (inverse r).2≤7000000000*RationalCostModel.schoolbook.rat (width N (inputSize i)) := by
  have hs:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hp:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sizes i r hr
  have hm0 : r.root.polynomial≠[] := by intro hz; exact hs.2.1.ne_zero (by rw [hz]; rfl)
  have hF : PlayerSpecificFiniteParameterSizes.height N (inputSize i)≤PlayerSpecificAlgebraicInitialInputSizes.base N (inputSize i) := by
    unfold PlayerSpecificAlgebraicInitialInputSizes.base; omega
  have hc:=PlayerSpecificAlgebraicInverseExecution.run_cost RationalCostModel.schoolbook r.root.polynomial r.scale hs.1 hm0 hs.2.2.1 hs.2.2.2.1
    (PlayerSpecificAlgebraicInitialInputSizes.base N (inputSize i)) (mono hp.1 hF) (mono hp.2.2.2.1 hF)
    (by unfold PlayerSpecificAlgebraicInitialInputSizes.base; omega)
  exact hc.trans (Nat.mul_le_mul_left 7000000000 (RationalCostModel.schoolbook.monotone (inverse_width N (inputSize i))))

theorem input_costs {N : ℕ} (i : RationalPlayerSpecificInput N) :
    (first i).2≤10000*(N+1)*RationalCostModel.schoolbook.rat (width N (inputSize i)) ∧
      (second i).2≤10000*(N+1)*RationalCostModel.schoolbook.rat (width N (inputSize i)) := by
  have hs:=PlayerSpecificRecognitionInputHeights.original_fields i
  have hv:=PlayerSpecificInputArrayExecution.source_cost RationalCostModel.schoolbook (inputSize i) i.valuesA.weight hs.2.1
  have hw:=PlayerSpecificInputArrayExecution.source_cost RationalCostModel.schoolbook (inputSize i) i.valuesB.weight hs.2.2
  have hm:=Nat.mul_le_mul_left (10000*(N+1)) (RationalCostModel.schoolbook.monotone (input_width N (inputSize i)))
  exact ⟨hv.trans hm,hw.trans hm⟩

theorem measurement_cost {N : ℕ} (i : RationalPlayerSpecificInput N) :
    (PlayerSpecificWidthExecution.run RationalCostModel.schoolbook (N+1)).2≤512*(N+1)*RationalCostModel.schoolbook.rat (width N (inputSize i)) :=
  (PlayerSpecificBitRatioSortBudget.measurement_cost RationalCostModel.schoolbook N (inputSize i)).trans
    (Nat.mul_le_mul_left (512*(N+1)) (RationalCostModel.schoolbook.monotone (input_width N (inputSize i))))

theorem frame_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    price RationalCostModel.schoolbook (PlayerSpecificAlgebraicInitialVectorExecution.frame i (inverse r).1)≤
      140*RationalCostModel.schoolbook.rat (width N (inputSize i)) := by
  have hs:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hm0 : r.root.polynomial≠[] := by intro hz; exact hs.2.1.ne_zero (by rw [hz]; rfl)
  have hiH:=(PlayerSpecificAlgebraicInitialInputSizes.actual_sizes i r hr).1
  have hiRed:=(PlayerSpecificAlgebraicInitialVector.reduced_rows RationalCostModel.schoolbook i r hs.1 hm0).1
  have hCW:=copy_width N (inputSize i)
  have hcache : HasHeight (inverse r).1 (PlayerSpecificAlgebraicInitialInputSizes.height N (inputSize i)) := by
    rw [inverse,PlayerSpecificAlgebraicInverseExecution.value]
    exact mono hiH (PlayerSpecificAlgebraicInitialStages.step_bounds _).1
  have hlen : (inverse r).1.length≤21 := by
    have hl:=hiRed.2
    have hml:=hs.2.2.1
    rw [inverse,PlayerSpecificAlgebraicInverseExecution.value]
    change (PlayerSpecificAlgebraicField.inverse r.root.polynomial r.scale).length<r.root.polynomial.length at hl
    omega
  have hiCopy:=PlayerSpecificExtendedCopyCost.row_cost RationalCostModel.schoolbook (inverse r).1 _ _ hcache hlen hCW.1 hCW.2.1
  have hbH:=((PlayerSpecificRecognitionInputHeights.original_fields i).1).mono (input_le_height N (inputSize i))
  have hbCopy:=PlayerSpecificExtendedCopyCost.row_cost RationalCostModel.schoolbook [i.budget] _ _
    (cons_height hbH (nil_height _)) (by simp) hCW.1 hCW.2.1
  have hn:=event_price RationalCostModel.schoolbook (width N (inputSize i)) (by omega) (.control N)
    ((control_width N).trans hCW.2.2)
  have hone:=event_price RationalCostModel.schoolbook (width N (inputSize i)) (by omega) (.control 1)
    ((control_width 1).trans (by omega))
  simp only [PlayerSpecificAlgebraicInitialVectorExecution.frame,price,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at *
  omega

end Blotto.PlayerSpecificAlgebraicInitialVectorStages
