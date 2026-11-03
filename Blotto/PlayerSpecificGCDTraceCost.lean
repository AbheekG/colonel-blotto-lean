import Blotto.PlayerSpecificEuclideanBudget

/-! Complete actual Euclidean GCD source price, including operand and
returned-polynomial copies. Bounds come from the original stored values. -/
namespace Blotto.PlayerSpecificGCDTraceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificGCDExecution PlayerSpecificEuclideanBudget
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem input_width (fuel H : ℕ) : 1+2*H≤width fuel H := by
  have h:=dense_width fuel H
  nlinarith

theorem header_cost (model : RationalCostModel) (fuel : ℕ) (p q : Data) (H W : ℕ)
    (hp : HasHeight p H) (hq : HasHeight q H) (hpl : p.length≤4) (hql : q.length≤4) (hf : fuel≤4)
    (hHW : 1+2*H≤W) (hW : 6≤W) : price model (header fuel p q)≤39*model.rat W := by
  have hpc := PlayerSpecificMonicDivisionBudget.copy_cost model p H W hp hpl hHW hW
  have hqc := PlayerSpecificMonicDivisionBudget.copy_cost model q H W hq hql hHW hW
  have hc := PlayerSpecificDenseTraceFits.controls_fits W [fuel,p.length,q.length] (by
    intro n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl <;> omega)
  have hcp := price_bound model W (by omega) _ hc
  simp only [List.map_cons,List.map_nil,List.length_cons,List.length_nil] at hcp
  rw [header,price_append,price_append]
  nlinarith

theorem loop_cost (model : RationalCostModel) (fuel : ℕ) (p q : Data) (H : ℕ)
    (hp : HasHeight p H) (hq : HasHeight q H) (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) (hcap : fuel≤4) :
    price model (loop fuel p q).2≤200000000*(fuel+1)*model.rat (width fuel H) := by
  induction fuel generalizing p q H with
  | zero =>
    have hW : 6≤width 0 H := (by decide : 6≤32).trans (width_large 0 H)
    have hh := header_cost model 0 p q H (width 0 H) hp hq hpl hql (by omega) (input_width 0 H) hW
    have ht := PlayerSpecificDenseOperationCost.trim_cost model p H 4 hp hpl
    rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at ht
    have htp : price model (PlayerSpecificDenseExecution.trim p).2≤375000*model.rat (width 0 H) :=
      ht.trans (Nat.mul_le_mul_left 375000 (model.monotone (dense_width 0 H)))
    have hf := PlayerSpecificMonicDivisionBudget.control_cost model 0 (width 0 H) (by omega) hW
    rw [loop,price_append,price_append]
    nlinarith
  | succ fuel ih =>
    have hW : 6≤width (fuel+1) H := (by decide : 6≤32).trans (width_large (fuel+1) H)
    have hh := header_cost model (fuel+1) p q H (width (fuel+1) H) hp hq hpl hql hcap (input_width (fuel+1) H) hW
    have hf0 := PlayerSpecificMonicDivisionBudget.control_cost model 0 (width (fuel+1) H) (by omega) hW
    have hf1 := PlayerSpecificMonicDivisionBudget.control_cost model 1 (width (fuel+1) H) (by omega) hW
    rw [loop]
    split
    · have ht := PlayerSpecificDenseOperationCost.trim_cost model p H 4 hp hpl
      rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at ht
      have htp : price model (PlayerSpecificDenseExecution.trim p).2≤375000*model.rat (width (fuel+1) H) :=
        ht.trans (Nat.mul_le_mul_left 375000 (model.monotone (dense_width (fuel+1) H)))
      simp only [price_append]
      have hm := Nat.mul_le_mul_right (model.rat (width (fuel+1) H)) (show 1≤fuel+1+1 by omega)
      nlinarith
    · let divided := PlayerSpecificDivisionExecution.run p q
      have hd := PlayerSpecificDivisionTraceCost.run_cost model p q H hp hq hH hpl hql
      have hdp : price model divided.2≤100000000*model.rat (width (fuel+1) H) :=
        hd.trans (Nat.mul_le_mul_left 100000000 (model.monotone (division_width (fuel+1) H)))
      have hrem : HasHeight divided.1.2 (step H) := (PlayerSpecificDivisionExecution.heights p q H hp hq hH hpl hql).2
      have hreml : divided.1.2.length≤4 := (PlayerSpecificDivisionExecution.lengths p q).2.trans hpl
      have hqnext := mono hq (step_ge H)
      have hstep : 1≤step H := hH.trans (step_ge H)
      have hfcap : fuel≤4 := by omega
      have hi := ih q divided.1.2 (step H) hqnext hrem hstep hql hreml hfcap
      let rest := loop fuel q divided.1.2
      have hip : price model rest.2≤200000000*(fuel+1)*model.rat (width (fuel+1) H) :=
        hi.trans (Nat.mul_le_mul_left (200000000*(fuel+1)) (model.monotone (next_width fuel H)))
      have hb := loop_bounds fuel q divided.1.2 (step H) hqnext hrem hstep hql hreml hfcap
      have hrH : HasHeight rest.1 (postHeight H) :=
        mono (s := PlayerSpecificExtendedGCDHeights.linearConstant*(step H+1)) (t := postHeight H) hb.1 (tail_height H)
      have hrl : rest.1.length≤4 := hb.2
      have hcopy := PlayerSpecificMonicDivisionBudget.copy_cost model rest.1 (postHeight H) (width (fuel+1) H)
        hrH hrl (copy_width (fuel+1) H) hW
      change price model (header (fuel+1) p q++divided.2++rest.2++copyRow rest.1++[.control 1])≤_
      simp only [price_append]
      nlinarith

def capWidth (H : ℕ) : ℕ := base*65536^5*(H+1)

theorem run_cost (model : RationalCostModel) (p q : Data) (H : ℕ)
    (hp : HasHeight p H) (hq : HasHeight q H) (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) :
    price model (run p q).2≤2000000000*model.rat (capWidth H) := by
  let divisor := PlayerSpecificDenseExecution.trim q
  have hdH : HasHeight divisor.1 H := by rw [PlayerSpecificDenseExecution.trim_value]; exact trim_height hq
  have hdl : divisor.1.length≤4 := by rw [PlayerSpecificDenseExecution.trim_value]; exact (trim_length q).trans hql
  have hc := loop_cost model divisor.1.length p divisor.1 H hp hdH hH hpl hdl hdl
  have hw := model.monotone (width_cap divisor.1.length H hdl)
  have hloop := hc.trans (Nat.mul_le_mul_left (200000000*(divisor.1.length+1)) hw)
  have hfactor := Nat.mul_le_mul_right (model.rat (capWidth H)) (show 200000000*(divisor.1.length+1)≤1000000000 by omega)
  have hloop' : price model (loop divisor.1.length p divisor.1).2≤1000000000*model.rat (capWidth H) := hloop.trans hfactor
  have hbase := PlayerSpecificDenseOperationCost.trim_cost model q H 4 hq hql
  rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at hbase
  have htrim : price model divisor.2≤375000*model.rat (capWidth H) :=
    hbase.trans (Nat.mul_le_mul_left 375000 (model.monotone ((dense_width 0 H).trans (width_cap 0 H (by omega)))))
  have hW : 6≤capWidth H := ((by decide : 6≤32).trans (width_large 0 H)).trans (width_cap 0 H (by omega))
  have hmeta := PlayerSpecificMonicDivisionBudget.control_cost model divisor.1.length (capWidth H) hdl hW
  change price model (divisor.2++(loop divisor.1.length p divisor.1).2++[.control divisor.1.length])≤_
  simp only [price_append]
  nlinarith

end Blotto.PlayerSpecificGCDTraceCost
