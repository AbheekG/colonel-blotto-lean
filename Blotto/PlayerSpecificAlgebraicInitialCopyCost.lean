import Blotto.PlayerSpecificAlgebraicInitialStages

/-! Complete retained/returned initial-data frame copies use the actual
fixed-degree stage heights and include the enclosing control word. -/
namespace Blotto.PlayerSpecificAlgebraicInitialCopyCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicInitialStages PlayerSpecificAlgebraicInitialPrimitiveCost
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem bounded_copy (model : RationalCostModel) (m : Data) (G : ℕ) (a : Data)
    (hml : m.length≤4) (ha : Bounded m G a) : price model (copyRow a)≤66*model.rat (width G) :=
  row_copy model a G ha.2 (by have hl:=ha.1.2; omega)

theorem frame_cost (model : RationalCostModel) (root : Candidate) (inverseScale : Data) (v w : ℚ) (G : ℕ)
    (hml : root.polynomial.length≤4) (hm : HasHeight root.polynomial G)
    (he : HasHeight [root.interval.lo,root.interval.hi] G) (hv : RationalHeight v G) (hw : RationalHeight w G)
    (hi : Bounded root.polynomial G inverseScale) (hs : Bounds model root inverseScale v w G) :
    price model (PlayerSpecificAlgebraicInitialExecution.frame root inverseScale v w
      (PlayerSpecificAlgebraicField.constant root.polynomial v) (PlayerSpecificAlgebraicInitial.weighted root w)
      (PlayerSpecificAlgebraicField.constant root.polynomial 1) (quotient model root v w)
      (PlayerSpecificAlgebraicInitial.run model root inverseScale v w))≤750*model.rat (width G) := by
  have hmcopy:=row_copy model root.polynomial G hm (by omega)
  have heq:=cons_height (head_height he) (cons_height (head_height (tail_height he)) (cons_height hv (cons_height hw (nil_height _))))
  have hecopy:=row_copy model [root.interval.lo,root.interval.hi,v,w] G heq (by simp)
  have hicopy:=bounded_copy model root.polynomial G inverseScale hml hi
  have hfcopy:=bounded_copy model root.polynomial G _ hml hs.first
  have hscopy:=bounded_copy model root.polynomial G _ hml hs.second
  have hucopy:=bounded_copy model root.polynomial G _ hml hs.unit
  have hqcopy:=bounded_copy model root.polynomial G _ hml hs.quotient
  have hlcopy:=bounded_copy model root.polynomial G _ hml hs.length
  have hacopy:=bounded_copy model root.polynomial G _ hml hs.initialA
  have hbcopy:=bounded_copy model root.polynomial G _ hml hs.initialB
  have hc:=event_price model (width G) (by have h:=large G; omega) (.control 1)
    ((control_width 1).trans (by have h:=large G; omega))
  change price model [.control 1]≤3*model.rat (width G) at hc
  simp only [PlayerSpecificAlgebraicInitialExecution.frame,price_append]
  nlinarith only [hmcopy,hecopy,hicopy,hfcopy,hscopy,hucopy,hqcopy,hlcopy,hacopy,hbcopy,hc]

end Blotto.PlayerSpecificAlgebraicInitialCopyCost
