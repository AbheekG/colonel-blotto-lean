import Blotto.PlayerSpecificIntegerPreparationCost

/-! Initial interval construction queries both cached endpoints and stores
their actual variation counts. Integer-to-rational conversion is charged at
the enclosing entry, alongside this complete rational/control trace. -/
namespace Blotto.PlayerSpecificInitialExecution
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run {p : Data} (prepared : Prepared p) (M : ℕ) : Interval×Trace :=
  let right : ℚ := M
  let left := scalar .multiply (-1) right
  let lower := PlayerSpecificEndpointExecution.endpoint prepared left.1
  let upper := PlayerSpecificEndpointExecution.endpoint prepared right
  let result : Interval := ⟨left.1,right,lower.1,upper.1⟩
  (result,[.copy right,.control M]++left.2++lower.2++upper.2++
    PlayerSpecificSplitExecution.copyInterval result++[.control prepared.sequence.length])

theorem value {p : Data} (prepared : Prepared p) (M : ℕ) :
    (run prepared M).1=initial prepared (-(M:ℚ)) (M:ℚ) := by
  simp only [run,scalar,Arithmetic.apply,neg_one_mul,PlayerSpecificEndpointExecution.endpoint_value,initial]

theorem run_cost (model : RationalCostModel) (p : Data) (prepared : Prepared p) (hlen : p.length≤4) :
    price model (run prepared (PlayerSpecificRootMagnitude.rootBound p)).2≤9000*model.rat (PlayerSpecificTraversalPrice.width p) := by
  let M:=PlayerSpecificRootMagnitude.rootBound p
  let H:=2*PlayerSpecificRationalMagnitude.inputHeight p+4
  let W:=PlayerSpecificTraversalPrice.width p
  let left:=scalar .multiply (-1) (M:ℚ)
  let lower:=PlayerSpecificEndpointExecution.endpoint prepared left.1
  let upper:=PlayerSpecificEndpointExecution.endpoint prepared (M:ℚ)
  let result : Interval:=⟨left.1,(M:ℚ),lower.1,upper.1⟩
  have hdepth : 0≤PlayerSpecificRootIsolation.depth p := Nat.zero_le _
  have heights:=PlayerSpecificDyadicEndpoints.endpoint_height p prepared (PlayerSpecificRootMagnitude.initial p prepared) 0
    (PlayerSpecificRootMagnitude.initial_valid p prepared) (PlayerSpecificDyadicEndpoints.initial_grid p prepared)
    (PlayerSpecificDyadicEndpoints.initial_bounded p prepared)
  have hright : RationalHeight (M:ℚ) H := heights.2
  have hleft : RationalHeight left.1 H := by
    simpa only [left,scalar,Arithmetic.apply,neg_one_mul] using hright.neg
  have hW : 6≤W := (by decide : 6≤600).trans (PlayerSpecificTraversalPrice.width_large p)
  have hHW : 1+2*H≤W := PlayerSpecificTraversalPrice.endpoint_width p hlen 0 hdepth
  have hminus : RationalHeight (-1:ℚ) H := PlayerSpecificPolynomialHeights.one_height.neg.mono (by unfold H; omega)
  have hfit:=scalar_fits W .multiply (-1) (M:ℚ)
    ((rationalWordWidth_of_height hminus).trans hHW)
    ((rationalWordWidth_of_height hright).trans hHW)
    (by simpa only [Arithmetic.apply,neg_one_mul] using (rationalWordWidth_of_height hright.neg).trans hHW) (by omega)
  have hscalar:=price_bound model W (by omega) _ hfit
  rw [scalar_length] at hscalar
  have hquery : PlayerSpecificPreparedQueryCost.queryWidth p H≤W := by
    have hc:=PlayerSpecificSquarefreeHeights.certificate_linear (PlayerSpecificRationalMagnitude.inputHeight p)
    unfold PlayerSpecificPreparedQueryCost.queryWidth PlayerSpecificPreparedQueryCost.queryHeight W H
      PlayerSpecificTraversalPrice.width PlayerSpecificTraversalPrice.widthCoefficient
    nlinarith
  have hl:=PlayerSpecificPreparedQueryCost.endpoint_cost model p prepared hlen left.1 H hleft
  have hh:=PlayerSpecificPreparedQueryCost.endpoint_cost model p prepared hlen (M:ℚ) H hright
  have hlp:=hl.trans (Nat.mul_le_mul_left 4000 (model.monotone hquery))
  have hhp:=hh.trans (Nat.mul_le_mul_left 4000 (model.monotone hquery))
  have hlcount : lower.1≤5 := PlayerSpecificPreparedQueryCost.endpoint_count p prepared hlen left.1
  have hhcount : upper.1≤5 := PlayerSpecificPreparedQueryCost.endpoint_count p prepared hlen (M:ℚ)
  have hcopy:=PlayerSpecificSplitTraceCost.copyInterval_cost model result H W hleft hright hlcount hhcount hHW hW
  have hMword : binaryWordWidth M≤W := by
    have hm : binaryWordWidth M=2*PlayerSpecificRationalMagnitude.inputHeight p+3 := PlayerSpecificIsolationDepthHeight.root_width p
    unfold H at hHW
    omega
  have hpre : Fits W [.copy (M:ℚ),.control M] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact (rationalWordWidth_of_height hright).trans hHW
    · exact hMword
  have hprep:=price_bound model W (by omega) _ hpre
  simp only [List.length_cons,List.length_nil] at hprep
  have hrows:=(PlayerSpecificPreparedQueryCost.prepared_bounds p prepared hlen).2
  have hlast : Fits W [.control prepared.sequence.length] := by
    intro e he
    have heq:=List.mem_singleton.mp he
    subst e
    exact (control_width _).trans (by omega)
  have hlastp:=price_bound model W (by omega) _ hlast
  simp only [List.length_cons,List.length_nil] at hlastp
  change price model ([.copy (M:ℚ),.control M]++left.2++lower.2++upper.2++
    PlayerSpecificSplitExecution.copyInterval result++[.control prepared.sequence.length])≤_
  simp only [price_append]
  change _≤9000*model.rat W
  nlinarith only [hscalar,hlp,hhp,hcopy,hprep,hlastp]

end Blotto.PlayerSpecificInitialExecution
