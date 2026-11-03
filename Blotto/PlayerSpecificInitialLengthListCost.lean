import Blotto.PlayerSpecificInitialLengthList

/-! Original-input source price of the cached length-list construction,
including actual measured indices, all coefficient/reference copies and
the backwards array-to-list loop. -/
namespace Blotto.PlayerSpecificInitialLengthListCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicInitialVectorBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

def stored {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) :=
  (PlayerSpecificAlgebraicInitialVectorExecution.run RationalCostModel.schoolbook i r).1
def table {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) :=
  PaperIndexedArrayConstruction.run RationalCostModel.schoolbook.rat (address N)
    (PlayerSpecificInitialLengthList.callback RationalCostModel.schoolbook (address N) p)
def polynomialCoefficient : ℕ := 20000*(widthCoefficient*widthCoefficient+widthCoefficient)

theorem callback_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) (j : Fin N) :
    (PlayerSpecificInitialLengthList.callback RationalCostModel.schoolbook (address N) (stored i r) j).2≤
      1000*RationalCostModel.schoolbook.rat (width N (inputSize i)) := by
  have hs:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  have hm0 : r.root.polynomial≠[] := by intro hz; exact hs.2.1.ne_zero (by rw [hz]; rfl)
  have hred:=((PlayerSpecificAlgebraicInitialVector.reduced_rows RationalCostModel.schoolbook i r hs.1 hm0).2 j).1
  have hheight:=((PlayerSpecificAlgebraicInitialVectorContract.output_heights i r hr).2 j).1
  have hlen : ((stored i r).rows.read j).length.length≤21 := by
    rw [stored,PlayerSpecificAlgebraicInitialVectorExecution.value]
    have hl:=hred.2
    have hm:=hs.2.2.1
    omega
  have hW:=copy_width N (inputSize i)
  have hc:=PlayerSpecificExtendedCopyCost.row_cost RationalCostModel.schoolbook ((stored i r).rows.read j).length
    (PlayerSpecificAlgebraicInitialInputSizes.height N (inputSize i)) (width N (inputSize i)) hheight hlen hW.1 hW.2.1
  have ha:=(address_bounds N (inputSize i)).2.1
  simp only [PlayerSpecificInitialLengthList.callback]
  nlinarith only [hc,ha]

theorem table_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    (table (stored i r)).2≤N*(1000*RationalCostModel.schoolbook.rat (width N (inputSize i)))+44*(N+1)*address N :=
  GeneralPaperControlArrayPrice.indexed_work _ _ _ _ (address_bounds N (inputSize i)).1
    (address_bounds N (inputSize i)).2.2 (callback_cost i r hr)

theorem price_eq {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) :
    (PlayerSpecificInitialLengthList.run RationalCostModel.schoolbook p).2=
      (PlayerSpecificWidthExecution.run RationalCostModel.schoolbook (N+1)).2+(table p).2+
        StoredArrayReferenceList.work RationalCostModel.schoolbook.rat (address N) N+64*(N+1)*address N+
          price RationalCostModel.schoolbook [.control N,.control 0] := by
  have hs : (table p).1.data.size=N := (table p).1.size
  simp only [PlayerSpecificInitialLengthList.run]
  change (PlayerSpecificWidthExecution.run RationalCostModel.schoolbook (N+1)).2+(table p).2+
    StoredArrayReferenceList.work RationalCostModel.schoolbook.rat (address N) (table p).1.data.size+
      64*(N+1)*address N+price RationalCostModel.schoolbook [.control N,.control 0]=_
  rw [hs]

theorem controls (N L : ℕ) : price RationalCostModel.schoolbook [.control N,.control 0]≤
    6*RationalCostModel.schoolbook.rat (width N L) := by
  have hw:=copy_width N L
  have hn:=event_price RationalCostModel.schoolbook (width N L) (by omega) (.control N) ((control_width N).trans hw.2.2)
  have hz:=event_price RationalCostModel.schoolbook (width N L) (by omega) (.control 0) ((control_width 0).trans (by omega))
  simp only [price,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

theorem source_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    (PlayerSpecificInitialLengthList.run RationalCostModel.schoolbook (stored i r)).2≤
      20000*(N+1)*RationalCostModel.schoolbook.rat (width N (inputSize i)) := by
  have ht:=table_cost i r hr
  have hm:=PlayerSpecificAlgebraicInitialVectorStages.measurement_cost i
  have href:=PlayerSpecificInitialLengthList.reference_work RationalCostModel.schoolbook N
  have ha:=(address_bounds N (inputSize i)).2.1
  have hc:=controls N (inputSize i)
  have hu:=Nat.mul_le_mul_right (RationalCostModel.schoolbook.rat (width N (inputSize i))) (show 1≤N+1 by omega)
  have haddr:=Nat.mul_le_mul_left (120*(N+1)) ha
  rw [price_eq]
  change StoredArrayReferenceList.work RationalCostModel.schoolbook.rat (address N) N≤12*(N+1)*address N at href
  nlinarith only [ht,hm,href,hc,hu,haddr]

theorem polynomial_cost {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    (PlayerSpecificInitialLengthList.run RationalCostModel.schoolbook (stored i r)).2≤
      polynomialCoefficient*(N+1)*size N (inputSize i)^2 :=
  (source_cost i r hr).trans (PlayerSpecificFiniteParameterCost.schoolbook_profile 20000 widthCoefficient (N+1)
    (size N (inputSize i)) (size_bounds N (inputSize i)).1)

end Blotto.PlayerSpecificInitialLengthListCost
