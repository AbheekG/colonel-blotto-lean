import Blotto.PlayerSpecificIntegerBudget

/-! Complete polynomial and integer root-preparation price, derived from
original encoding. Returned polynomial and integer fields are all copied. -/
namespace Blotto.PlayerSpecificIntegerPreparationCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalMagnitude
open PlayerSpecificSquarefreeHeights PlayerSpecificIntegerPreparation PlayerSpecificIntegerBudget PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem run_cost (model : RationalCostModel) (p : Data) (hlen : p.length≤4) :
    (run model p).2≤20000000000*(height (inputHeight p)+1)*model.rat (width (inputHeight p)) := by
  let H:=inputHeight p
  let J:=height H
  let W:=width H
  let prepared:=PlayerSpecificPolynomialPreparation.run p
  let originalWidth:=PlayerSpecificInputWidthExecution.run model p
  let squarefreeWidth:=PlayerSpecificInputWidthExecution.run model prepared.1.polynomial
  let certificateWidth:=PlayerSpecificInputWidthExecution.run model prepared.1.unitRight
  let magnitude:=PlayerSpecificEnclosureExecution.run model originalWidth.1
  let precision:=PlayerSpecificDepthExecution.run model magnitude.1 squarefreeWidth.1 certificateWidth.1 prepared.1.unitRight.length
  have hp:=input_height p
  have hH : 1≤H := by unfold H inputHeight; omega
  have hJ : 1≤J := hH.trans (input_le H)
  have hv:=PlayerSpecificPolynomialPreparation.values p
  have hq:=quotient_bounds p H hp hH hlen
  have hu:=unitRight_bounds p H hp hH hlen
  have hpJ : HasHeight p J := mono hp (input_le H)
  have hqJ : HasHeight prepared.1.polynomial J := by
    rw [hv.1]
    exact mono hq.1 ((quotient_linear H).trans (quotient_le H))
  have huJ : HasHeight prepared.1.unitRight J := by
    rw [hv.2.1]
    have hm:=Nat.mul_le_mul_left 2 (certificate_linear H)
    exact mono hu.1 (hm.trans (by simpa only [Nat.mul_assoc] using unit_le H))
  have hql : prepared.1.polynomial.length≤4 := by rw [hv.1]; exact hq.2
  have hul : prepared.1.unitRight.length≤17 := by rw [hv.2.1]; exact hu.2
  have hrJ : ∀ row∈prepared.1.rows,HasHeight row J ∧ row.length≤4 := by
    rw [hv.2.2]
    intro row hr
    have hh:=PlayerSpecificSturmHeights.rows_bounds p H hp hH hlen row hr
    exact ⟨mono hh.1 ((certificate_linear H).trans (certificate_le H)),hh.2⟩
  have hrl : prepared.1.rows.length≤5 := by rw [hv.2.2]; exact PlayerSpecificSturmHeights.rows_length p H hp hH hlen
  have hpoly:=PlayerSpecificPolynomialPreparation.run_cost model p H hp hH hlen
  have hpolyp:=hpoly.trans (Nat.mul_le_mul_left 10000000000 (model.monotone (polynomial_width H)))
  have hmeasurep:=PlayerSpecificInputWidthCost.run_cost model p J hpJ (by omega)
  have hmeasureq:=PlayerSpecificInputWidthCost.run_cost model prepared.1.polynomial J hqJ (by omega)
  have hmeasureu:=PlayerSpecificInputWidthCost.run_cost model prepared.1.unitRight J huJ hul
  have hmw:=model.monotone (measurement_width H J (by rfl))
  have hmp:=hmeasurep.trans (Nat.mul_le_mul_left (40000*(J+1)) hmw)
  have hmq:=hmeasureq.trans (Nat.mul_le_mul_left (40000*(J+1)) hmw)
  have hmu:=hmeasureu.trans (Nat.mul_le_mul_left (40000*(J+1)) hmw)
  have ho : originalWidth.1=H := PlayerSpecificInputWidthExecution.value model p
  have hm:=PlayerSpecificEnclosureExecution.run_cost model originalWidth.1
  have hmWidth : PlayerSpecificEnclosureExecution.width originalWidth.1≤W := by
    rw [ho]
    exact enclosure_width H
  have hmFactor : 4096*(originalWidth.1+1)≤4096*(J+1) := by
    rw [ho]
    exact Nat.mul_le_mul_left 4096 (Nat.add_le_add_right (input_le H) 1)
  have hmW:=hm.trans (Nat.mul_le_mul_left (4096*(originalWidth.1+1)) (model.monotone hmWidth))
  have hmP:=hmW.trans (Nat.mul_le_mul_right (model.rat W) hmFactor)
  have hsize : PlayerSpecificSeparationExecution.size magnitude.1 squarefreeWidth.1 certificateWidth.1≤J := by
    rw [show magnitude.1=PlayerSpecificRootMagnitude.rootBound p from magnitude_value model p,
      PlayerSpecificInputWidthExecution.value,PlayerSpecificInputWidthExecution.value,hv.1,hv.2.1]
    exact separation_size p hlen
  have hsepW : PlayerSpecificSeparationExecution.width magnitude.1 squarefreeWidth.1 certificateWidth.1≤W := by
    unfold PlayerSpecificSeparationExecution.width W width
    omega
  have hd:=PlayerSpecificDepthExecution.run_cost model magnitude.1 squarefreeWidth.1 certificateWidth.1 prepared.1.unitRight.length hul
  have hdW:=hd.trans (Nat.mul_le_mul_left (2000000*PlayerSpecificSeparationExecution.size magnitude.1 squarefreeWidth.1 certificateWidth.1)
    (model.monotone hsepW))
  have hdP:=hdW.trans (Nat.mul_le_mul_right (model.rat W) (Nat.mul_le_mul_left 2000000 (show PlayerSpecificSeparationExecution.size magnitude.1 squarefreeWidth.1 certificateWidth.1≤J+1 by omega)))
  have hW : 32≤W := width_large H
  have hcopyq:=PlayerSpecificExtendedCopyCost.row_cost model prepared.1.polynomial J W hqJ (by omega) (copy_width H J (by rfl)) hW
  have hcopyu:=PlayerSpecificExtendedCopyCost.row_cost model prepared.1.unitRight J W huJ (by omega) (copy_width H J (by rfl)) hW
  have hcopyr:=PlayerSpecificSturmCopyCost.copyRows_cost model prepared.1.rows J W hrJ hrl (copy_width H J (by rfl)) hW
  have hmag : binaryWordWidth magnitude.1≤2*H+3 := by
    rw [show magnitude.1=PlayerSpecificRootMagnitude.rootBound p from magnitude_value model p,
      PlayerSpecificIsolationDepthHeight.root_width]
  have hsep : binaryWordWidth precision.1.1≤20*J := by
    rw [show precision.1.1=PlayerSpecificRootSeparation.separationDenominator p from separation_value model p]
    exact separation_word p hlen
  have hdepth : precision.1.2≤J := by
    rw [show precision.1.2=PlayerSpecificRootIsolation.depth p from depth_value model p]
    exact (PlayerSpecificIsolationDepthHeight.depth_linear p hlen).trans (depth_le H)
  have hdword:=PlayerSpecificRationalTrace.control_width precision.1.2
  have hlenword:=PlayerSpecificRationalTrace.control_width p.length
  have hi:=input_le H
  have hmeta : 32*(4+binaryWordWidth p.length+binaryWordWidth magnitude.1+
      binaryWordWidth precision.1.1+binaryWordWidth precision.1.2)≤2048*(J+1) := by omega
  have hP : 1≤model.rat W := (by omega : 1≤W).trans (model.word_le W)
  have hmetap:=hmeta.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2048*(J+1)) hP)
  change price model prepared.2+originalWidth.2+squarefreeWidth.2+certificateWidth.2+magnitude.2+precision.2+
    price model (copyRow prepared.1.polynomial++copyRow prepared.1.unitRight++PlayerSpecificSturmExecution.copyRows prepared.1.rows)+
    32*(4+binaryWordWidth p.length+binaryWordWidth magnitude.1+binaryWordWidth precision.1.1+binaryWordWidth precision.1.2)≤_
  simp only [price_append]
  change _≤20000000000*(J+1)*model.rat W
  nlinarith only [hpolyp,hmp,hmq,hmu,hmP,hdP,hcopyq,hcopyu,hcopyr,hmetap]

end Blotto.PlayerSpecificIntegerPreparationCost
