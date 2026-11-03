import Blotto.PlayerSpecificCancellationExecution

/-! The actual cubic leading-cancellation trace has a constant number of
linear-width rational operations. All intermediate heights/list lengths
are derived here from the source inputs and cached executed term. -/
namespace Blotto.PlayerSpecificCancellationTraceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

def width (H : ℕ) : ℕ := 1024*(H+1)

theorem run_cost (model : RationalCostModel) (p q : Data) (H : ℕ)
    (hp : HasHeight p H) (hq : HasHeight q H) (hH : 1≤H)
    (hpl : p.length≤4) (hql : q.length≤4) (hp0 : p≠[]) (hq0 : q≠[]) :
    price model (PlayerSpecificCancellationExecution.run p q).2≤5000000*model.rat (width H) := by
  let term := PlayerSpecificTermExecution.run p q
  let product := PlayerSpecificDenseExecution.multiply q term.1
  let difference := PlayerSpecificDenseExecution.subtract p product.1
  let normalized := PlayerSpecificDenseExecution.trim difference.1
  have htH : HasHeight term.1 H := PlayerSpecificTermExecution.height p q H hp hH
  have htl : term.1.length≤4 := (PlayerSpecificTermExecution.length_le p q hp0 hq0).trans hpl
  have hprod : HasHeight product.1 (10*H+5) := by
    dsimp only [product]
    rw [PlayerSpecificDenseExecution.multiply_value]
    apply mono (multiply_height hq htH)
    have hm := Nat.mul_le_mul_left (H+H+1) (Nat.add_le_add_right hql 1)
    nlinarith
  have hprodlen : product.1.length≤8 := by
    dsimp only [product]
    rw [PlayerSpecificDenseExecution.multiply_value]
    exact (PlayerSpecificDensePolynomial.multiply_length q term.1).trans (by omega)
  have hdiff : HasHeight difference.1 (11*H+6) := by
    dsimp only [difference]
    rw [PlayerSpecificDenseExecution.subtract_value]
    have h := subtract_height hp hprod
    have he : H+(10*H+5)+1=11*H+6 := by omega
    simpa only [he] using h
  have hdifflen : difference.1.length≤8 := by
    dsimp only [difference]
    rw [PlayerSpecificDenseExecution.subtract_value,PlayerSpecificDensePolynomial.subtract,
      PlayerSpecificDensePolynomial.add_length,PlayerSpecificDensePolynomial.scale_length]
    exact max_le (by omega) hprodlen
  have htbase := PlayerSpecificTermExecution.cost model p q H 4 hp hq hH hpl hql
  have htprice : price model term.2≤7500*model.rat (width H) :=
    htbase.trans (Nat.mul_le_mul_left 7500 (model.monotone (by unfold PlayerSpecificTermExecution.width width; omega)))
  have hpbase := PlayerSpecificDenseOperationCost.multiply_cost model q term.1 H 4 hq htH hql htl
  rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at hpbase
  have hpprice : price model product.2≤375000*model.rat (width H) :=
    hpbase.trans (Nat.mul_le_mul_left 375000 (model.monotone (by unfold width; omega)))
  have hdbase := PlayerSpecificDenseOperationCost.subtract_cost model p product.1 (10*H+5) 8
    (mono hp (by omega)) hprod (by omega) (by omega) hprodlen
  change price model difference.2≤2187000*model.rat (PlayerSpecificCompositeTraceFits.width (10*H+5) 8) at hdbase
  have hdprice : price model difference.2≤2187000*model.rat (width H) :=
    hdbase.trans (Nat.mul_le_mul_left 2187000 (model.monotone (by
      unfold PlayerSpecificCompositeTraceFits.width PlayerSpecificCompositeTraceFits.height width
      nlinarith)))
  have hnbase := PlayerSpecificDenseOperationCost.trim_cost model difference.1 (11*H+6) 8 hdiff hdifflen
  change price model normalized.2≤2187000*model.rat (PlayerSpecificCompositeTraceFits.width (11*H+6) 8) at hnbase
  have hnprice : price model normalized.2≤2187000*model.rat (width H) :=
    hnbase.trans (Nat.mul_le_mul_left 2187000 (model.monotone (by
      unfold PlayerSpecificCompositeTraceFits.width PlayerSpecificCompositeTraceFits.height width
      nlinarith)))
  have hc : Fits (width H) [.control p.length,.control q.length] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl <;> exact (control_width _).trans (by unfold width; omega)
  have hmeta := price_bound model (width H) (by unfold width; omega) _ hc
  simp only [List.length_cons,List.length_nil] at hmeta
  change price model (term.2++product.2++difference.2++normalized.2++[.control p.length,.control q.length])≤_
  simp only [price_append]
  nlinarith

end Blotto.PlayerSpecificCancellationTraceCost
