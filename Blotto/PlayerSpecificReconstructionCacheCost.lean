import Blotto.PlayerSpecificReconstructionCacheBudget

/-! Complete source price of cached original-input reconstruction controls,
polynomials, powers and copied output fields. All bounds are derived. -/
namespace Blotto.PlayerSpecificReconstructionCacheCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalMagnitude PlayerSpecificRationalTrace
open PlayerSpecificIntegerBudget PlayerSpecificReconstructionCacheBudget
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem run_cost (model : RationalCostModel) (p : Data) (hlen : p.length≤4) :
    (PlayerSpecificReconstructionCache.run model p).2≤21000000000*(height (inputHeight p)+1)*model.rat (width (inputHeight p)) := by
  let H:=inputHeight p
  let J:=height H
  let W:=width H
  let d:=PlayerSpecificRootIsolation.depth p
  let F:=d+(14*H+12)
  let prepared:=PlayerSpecificIntegerPreparation.run model p
  have hb:=controls p hlen
  have hH : H≤J := hb.1
  have hseven : 7*H+4≤J := hb.2.1
  have hfourteen : 14*H+12≤J := hb.2.2.1
  have hd : d≤J := hb.2.2.2.1
  have hF : F+3≤J := by
    have he : F=PlayerSpecificReconstructionPrecision.depth p := by rw [PlayerSpecificReconstructionCache.depth_formula]; dsimp only [F,d]; ring
    rw [he]
    exact hb.2.2.2.2
  have b1:=binary_cost model H (fun a b => a*b) 7 H (by omega) (by omega) (by omega)
  have b2:=binary_cost model H (fun a b => a+b) (7*H) 3 (by omega) (by omega) (by omega)
  have b3:=binary_cost model H (fun a b => a*b) 14 H (by omega) (by omega) (by omega)
  have b4:=binary_cost model H (fun a b => a+b) (14*H) 12 (by omega) (by omega) (by omega)
  have b5:=binary_cost model H (fun a b => a+b) d (14*H+12) (by omega) (by omega) (by omega)
  have b6:=binary_cost model H (fun a b => a+b) F 3 (by omega) (by omega) (by omega)
  have b7:=binary_cost model H (fun a b => a+b) (7*H+3) 1 (by omega) (by omega) (by omega)
  have b8:=binary_cost model H (fun a b => a+b) H (F+3) (by omega) (by omega) (by omega)
  have b9:=binary_cost model H (fun a b => a+b) (H+(F+3)) (7*H+3+1) (by omega) (by omega) (by omega)
  have b10:=binary_cost model H (fun a b => a+b) (H+(F+3)+(7*H+3+1)) 1 (by omega) (by omega) (by omega)
  have b11:=binary_cost model H (fun a b => a*b) 4096 (H+(F+3)+(7*H+3+1)+1) (by omega) (by omega) (by omega)
  have powerD:=dyadic_cost model H (7*H+3) (by omega)
  have powerC:=dyadic_cost model H F (by omega)
  have hprep:=PlayerSpecificIntegerPreparationCost.run_cost model p hlen
  have hread0:=PlayerSpecificInputWidthCost.run_cost model p J (mono (input_height p) hH) (by omega)
  have hread:=hread0.trans (Nat.mul_le_mul_left (40000*(J+1)) (model.monotone (measurement_width H J (by rfl))))
  have hv:=PlayerSpecificIntegerPreparation.polynomial_values model p
  have hHpos : 1≤H := by unfold H inputHeight; omega
  have hq:=PlayerSpecificSquarefreeHeights.quotient_bounds p H (input_height p) hHpos hlen
  have hu:=PlayerSpecificSquarefreeHeights.unitRight_bounds p H (input_height p) hHpos hlen
  have hqJ : HasHeight prepared.1.polynomials.polynomial J := by
    rw [hv.1]
    exact mono hq.1 ((PlayerSpecificSquarefreeHeights.quotient_linear H).trans (quotient_le H))
  have huJ : HasHeight prepared.1.polynomials.unitRight J := by
    rw [hv.2.1]
    have hm:=Nat.mul_le_mul_left 2 (PlayerSpecificSquarefreeHeights.certificate_linear H)
    exact mono hu.1 (hm.trans (by simpa only [Nat.mul_assoc] using unit_le H))
  have hql : prepared.1.polynomials.polynomial.length≤21 := by rw [hv.1]; omega
  have hul : prepared.1.polynomials.unitRight.length≤21 := by rw [hv.2.1]; omega
  have hrJ : ∀ row∈prepared.1.polynomials.rows,HasHeight row J ∧ row.length≤4 := by
    rw [hv.2.2]
    intro row hr
    have hh:=PlayerSpecificSturmHeights.rows_bounds p H (input_height p) hHpos hlen row hr
    exact ⟨mono hh.1 ((PlayerSpecificSquarefreeHeights.certificate_linear H).trans (certificate_le H)),hh.2⟩
  have hrl : prepared.1.polynomials.rows.length≤5 := by
    rw [hv.2.2]
    exact PlayerSpecificSturmHeights.rows_length p H (input_height p) hHpos hlen
  have hW : 32≤W := width_large H
  have cq:=PlayerSpecificExtendedCopyCost.row_cost model prepared.1.polynomials.polynomial J W hqJ hql (copy_width H J (by rfl)) hW
  have cu:=PlayerSpecificExtendedCopyCost.row_cost model prepared.1.polynomials.unitRight J W huJ hul (copy_width H J (by rfl)) hW
  have cr:=PlayerSpecificSturmCopyCost.copyRows_cost model prepared.1.polynomials.rows J W hrJ hrl (copy_width H J (by rfl)) hW
  have hmag : binaryWordWidth prepared.1.magnitude=2*H+3 := by
    rw [PlayerSpecificIntegerPreparation.magnitude_value,PlayerSpecificIsolationDepthHeight.root_width]
  have hsep : binaryWordWidth prepared.1.separation≤20*J := by
    rw [PlayerSpecificIntegerPreparation.separation_value]
    exact separation_word p hlen
  have hdepthword:=control_width d
  have hHword:=control_width H
  have hFword:=control_width F
  have hLword:=control_width (F+3)
  have hpad:=control_width (H+(F+3)+(7*H+3+1)+1)
  have hword:=binaryWordWidth_mul 4096 (H+(F+3)+(7*H+3+1)+1)
  have h4096 : binaryWordWidth 4096=13 := by decide
  have hmeta : 64*(([prepared.1.magnitude,prepared.1.separation,d,H,2^(7*H+3),F,2^F,F+3,
      4096*(H+(F+3)+(7*H+3+1)+1)].map (fun n => 1+binaryWordWidth n)).sum)≤8192*(J+1) := by
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      PlayerSpecificIsolationDepthHeight.two_power_width]
    omega
  have hP : 1≤model.rat W := (by omega : 1≤W).trans (model.word_le W)
  have hmetap:=hmeta.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (8192*(J+1)) hP)
  rw [PlayerSpecificReconstructionCache.run]
  simp only [PlayerSpecificNaturalExecution.binary_value,PlayerSpecificNaturalExecution.power_value,
    PlayerSpecificInputWidthExecution.value,PlayerSpecificIntegerPreparation.depth_value,price_append]
  change _≤21000000000*(J+1)*model.rat W
  nlinarith only [b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,powerD,powerC,hprep,hread,cq,cu,cr,hmetap]

end Blotto.PlayerSpecificReconstructionCacheCost
