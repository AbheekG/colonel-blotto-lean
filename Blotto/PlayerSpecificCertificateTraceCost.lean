import Blotto.PlayerSpecificCertificateExecution

/-! Unit-certificate preparation prices include the actual head inverse,
all seventeen possible right-certificate coefficients and returned copies. -/
namespace Blotto.PlayerSpecificCertificateTraceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificSquarefreeHeights PlayerSpecificPreparationBudget PlayerSpecificCertificateExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem certificate_cost (model : RationalCostModel) (h : Data) (J : ℕ)
    (hh : HasHeight h J) (hJ : 1≤J) (hlen : h.length≤4) :
    price model (certificate h).2≤3000000000*model.rat (PlayerSpecificGCDTraceCost.capWidth (5*(J+1))) := by
  let differentiated := PlayerSpecificDenseExecution.derivative h
  have hdH : HasHeight differentiated.1 (5*(J+1)) := by
    rw [PlayerSpecificDenseExecution.derivative_value]
    exact derivative_height_four h J hh hlen
  have hdl : differentiated.1.length≤4 := by
    rw [PlayerSpecificDenseExecution.derivative_value]
    exact (derivative_length h).trans hlen
  have hd := PlayerSpecificDenseOperationCost.derivative_cost model h J 4 hh hlen
  rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at hd
  have hw : 40*J+64≤PlayerSpecificGCDTraceCost.capWidth (5*(J+1)) := by
    apply le_trans ?_ ((PlayerSpecificEuclideanBudget.dense_width 0 (5*(J+1))).trans
      (PlayerSpecificEuclideanBudget.width_cap 0 (5*(J+1)) (by omega)))
    omega
  have hdp := hd.trans (Nat.mul_le_mul_left 375000 (model.monotone hw))
  have he := PlayerSpecificExtendedGCDTraceCost.run_cost model h differentiated.1 (5*(J+1))
    (mono hh (by omega)) hdH (by omega) hlen hdl
  have hW : 6≤PlayerSpecificGCDTraceCost.capWidth (5*(J+1)) := by omega
  have hc := PlayerSpecificMonicDivisionBudget.control_cost model h.length _ hlen hW
  change price model (differentiated.2++(PlayerSpecificExtendedGCDExecution.run h differentiated.1).2++[.control h.length])≤_
  simp only [price_append]
  nlinarith

theorem normalize_cost (model : RationalCostModel) (result : PlayerSpecificExtendedGCD.Result) (T W : ℕ)
    (hg : HasHeight result.gcd T) (hr : HasHeight result.right T) (hT : 1≤T)
    (hgl : result.gcd.length≤4) (hrl : result.right.length≤17)
    (hw : PlayerSpecificCompositeTraceFits.width T 17≤W) :
    price model (normalize result).2≤20000000*model.rat W := by
  let inverted := PlayerSpecificHeadInverseExecution.run result.gcd
  let scaled := PlayerSpecificDenseExecution.scale inverted.1 result.right
  have hiH : RationalHeight inverted.1 T := PlayerSpecificHeadInverseExecution.height result.gcd T hg hT
  have hi := PlayerSpecificHeadInverseExecution.run_cost model result.gcd T 4 hg hT hgl
  have hwi : PlayerSpecificHeadInverseExecution.width T 4≤W := by
    unfold PlayerSpecificHeadInverseExecution.width PlayerSpecificCompositeTraceFits.width PlayerSpecificCompositeTraceFits.height at *
    nlinarith
  have hip := hi.trans (Nat.mul_le_mul_left (3*(4+8)) (model.monotone hwi))
  have hs := PlayerSpecificDenseOperationCost.scale_cost model inverted.1 result.right T 17 hiH hr hrl
  change price model scaled.2≤17496000*model.rat (PlayerSpecificCompositeTraceFits.width T 17) at hs
  have hsp := hs.trans (Nat.mul_le_mul_left 17496000 (model.monotone hw))
  have hout : HasHeight scaled.1 (2*T) := by
    rw [PlayerSpecificDenseExecution.scale_value]
    simpa only [two_mul] using scale_height hiH hr
  have hol : scaled.1.length≤17 := by rw [PlayerSpecificDenseExecution.scale_value,scale_length]; exact hrl
  have hW : 32≤W := by
    unfold PlayerSpecificCompositeTraceFits.width PlayerSpecificCompositeTraceFits.height at hw
    nlinarith
  have hwcopy : 1+2*(2*T)≤W := by
    unfold PlayerSpecificCompositeTraceFits.width PlayerSpecificCompositeTraceFits.height at hw
    nlinarith
  have hcopy := PlayerSpecificExtendedCopyCost.row_cost model scaled.1 (2*T) W hout (by omega) hwcopy hW
  have hf := PlayerSpecificDenseTraceFits.controls_fits W [result.right.length] (by
    intro n hn
    have he:=List.mem_singleton.mp hn
    subst n
    omega)
  have hc := price_bound model W (by omega) _ hf
  simp only [List.map_cons,List.map_nil,List.length_cons,List.length_nil] at hc
  change price model (inverted.2++scaled.2++copyRow scaled.1++[.control result.right.length])≤_
  simp only [price_append]
  nlinarith

theorem run_cost (model : RationalCostModel) (p : Data) (H : ℕ)
    (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤4) :
    price model (run p).2≤7000000000*model.rat (width H) := by
  let squarefree := PlayerSpecificSquarefreeExecution.run p
  let computed := certificate squarefree.1
  let unit := normalize computed.1
  have hsf := PlayerSpecificSquarefreeExecution.bounds p H hp hH hlen
  have hQ : 1≤quotientHeight H := hH.trans (quotientHeight_ge H)
  have hC : 1≤certificateHeight H := hQ.trans (gcdHeight_ge (quotientHeight H))
  have hcv : computed.1=PlayerSpecificSquarefreeCoprime.certificate p := by
    simp only [computed,certificate_value,squarefree,PlayerSpecificSquarefreeExecution.value,PlayerSpecificSquarefreeCoprime.certificate]
  have hcert := certificate_bounds p H hp hH hlen
  have hg : HasHeight computed.1.gcd (certificateHeight H) := by rw [hcv]; exact hcert.1
  have hr : HasHeight computed.1.right (certificateHeight H) := by rw [hcv]; exact hcert.2.1
  have hrl : computed.1.right.length≤17 := by rw [hcv]; exact hcert.2.2
  have he := PlayerSpecificExtendedGCDHeights.run_bounds squarefree.1 (derivative squarefree.1) (5*(quotientHeight H+1))
    (mono hsf.1 (by omega)) (derivative_height_four squarefree.1 _ hsf.1 hsf.2) (by omega)
    hsf.2 ((derivative_length squarefree.1).trans hsf.2)
  have hgl : computed.1.gcd.length≤4 := by rw [certificate_value]; exact he.2.2.2.1
  have hs := PlayerSpecificSquarefreeTraceCost.run_cost model p H hp hH hlen
  have hc := certificate_cost model squarefree.1 (quotientHeight H) hsf.1 hQ hsf.2
  have hcp := hc.trans (Nat.mul_le_mul_left 3000000000 (model.monotone (cap_width H _ (certificate_input H))))
  have hn := normalize_cost model computed.1 (certificateHeight H) (width H) hg hr hC hgl hrl
    (composite_width H _ 17 (certificate_height H) (by omega))
  have hW := width_large H
  have hcopy := PlayerSpecificMonicDivisionBudget.copy_cost model squarefree.1 (quotientHeight H) (width H)
    hsf.1 hsf.2 (copy_width H _ (quotient_height H)) (by omega)
  have hul : unit.1.length≤17 := by
    rw [normalize_value,scale_length]
    exact hrl
  have hf := PlayerSpecificDenseTraceFits.controls_fits (width H) [unit.1.length] (by
    intro n hn
    have heq:=List.mem_singleton.mp hn
    subst n
    omega)
  have hmeta := price_bound model (width H) (by omega) _ hf
  simp only [List.map_cons,List.map_nil,List.length_cons,List.length_nil] at hmeta
  change price model (squarefree.2++computed.2++unit.2++copyRow squarefree.1++[.control unit.1.length])≤_
  simp only [price_append]
  nlinarith

end Blotto.PlayerSpecificCertificateTraceCost
