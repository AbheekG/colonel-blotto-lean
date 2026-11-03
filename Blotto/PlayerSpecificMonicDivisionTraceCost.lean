import Blotto.PlayerSpecificMonicDivisionBudget

/-! Recursive source-price composition for actual monic division. The fuel,
coefficient sizes and intermediate list lengths are checked from source
inputs and the previously proved cancellation/height/degree properties. -/
namespace Blotto.PlayerSpecificMonicDivisionTraceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace PlayerSpecificMonicDivisionExecution PlayerSpecificMonicDivisionBudget
set_option autoImplicit false
set_option maxHeartbeats 7000000

theorem run_cost (model : RationalCostModel) (q : Data) (fuel : ℕ) (p : Data) (H : ℕ)
    (hqn : Normalized q) (hqm : (semantics q).Monic) (hql : q.length≤4)
    (hp : HasHeight p H) (hq : HasHeight q H) (hH : 1≤H) (hpl : p.length≤4) (hcap : fuel≤4) :
    price model (run q fuel p).2≤10000000*(fuel+1)*model.rat (width fuel H) := by
  have hq0 : q≠[] := by intro hz; apply hqm.ne_zero; rw [hz]; rfl
  induction fuel generalizing p H with
  | zero =>
    let current := PlayerSpecificDenseExecution.trim p
    have hcH : HasHeight current.1 H := by rw [PlayerSpecificDenseExecution.trim_value]; exact trim_height hp
    have hcl : current.1.length≤4 := by rw [PlayerSpecificDenseExecution.trim_value]; exact (trim_length p).trans hpl
    have hw := width_large 0 H
    have hdw := dense_width 0 H
    have ht := PlayerSpecificDenseOperationCost.trim_cost model p H 4 hp hpl
    rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at ht
    have ht' : price model current.2≤375000*model.rat (width 0 H) :=
      ht.trans (Nat.mul_le_mul_left 375000 (model.monotone hdw))
    have hh := header_cost model q current.1 0 H (width 0 H) hq hql hcl (by omega) (by omega) hw
    have he := copy_cost model [] H (width 0 H) (nil_height _) (by simp only [List.length_nil]; omega) (by omega) hw
    have hf := control_cost model 0 (width 0 H) (by omega) hw
    change price model (current.2++header q 0 current.1++copyRow []++[.control 0])≤_
    simp only [price_append]
    nlinarith
  | succ fuel ih =>
    let current := PlayerSpecificDenseExecution.trim p
    have hcH : HasHeight current.1 H := by rw [PlayerSpecificDenseExecution.trim_value]; exact trim_height hp
    have hcl : current.1.length≤4 := by rw [PlayerSpecificDenseExecution.trim_value]; exact (trim_length p).trans hpl
    have hcn : Normalized current.1 := by rw [PlayerSpecificDenseExecution.trim_value]; exact trim_normalized _
    have hw := width_large (fuel+1) H
    have hdw := dense_width (fuel+1) H
    have ht := PlayerSpecificDenseOperationCost.trim_cost model p H 4 hp hpl
    rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at ht
    have ht' : price model current.2≤375000*model.rat (width (fuel+1) H) :=
      ht.trans (Nat.mul_le_mul_left 375000 (model.monotone hdw))
    have hh := header_cost model q current.1 (fuel+1) H (width (fuel+1) H) hq hql hcl hcap (by omega) hw
    have he := copy_cost model [] H (width (fuel+1) H) (nil_height _) (by simp only [List.length_nil]; omega) (by omega) hw
    have hf0 := control_cost model 0 (width (fuel+1) H) (by omega) hw
    have hf1 := control_cost model 1 (width (fuel+1) H) (by omega) hw
    rw [run]
    split
    · change price model (current.2++header q (fuel+1) current.1++copyRow []++[.control 0])≤_
      simp only [price_append]
      have hm := Nat.mul_le_mul_right (model.rat (width (fuel+1) H)) (show 1≤fuel+1+1 by omega)
      nlinarith
    · rename_i hgo
      have hp0 : current.1≠[] := (not_or.mp hgo).1
      have hlen : q.length≤current.1.length := le_of_not_gt (not_or.mp hgo).2
      let canceled := PlayerSpecificCancellationExecution.run current.1 q
      have hterm : HasHeight canceled.1.1 H := PlayerSpecificCancellationExecution.term_height current.1 q H hcH hH
      have htermlen : canceled.1.1.length≤4 := (PlayerSpecificCancellationExecution.term_length current.1 q hp0 hq0).trans hcl
      have hrem : HasHeight canceled.1.2 (step H) := PlayerSpecificCancellationExecution.remainder_height current.1 q H hcH hq hH hql
      have hdrop : canceled.1.2.length<current.1.length :=
        PlayerSpecificCancellationExecution.drops_length current.1 q hcn hqn hp0 hqm hlen
      have hremLen : canceled.1.2.length≤4 := by omega
      have hqnH := mono hq (step_ge H)
      have hstep : 1≤step H := hH.trans (step_ge H)
      have hfcap : fuel≤4 := by omega
      have hi := ih canceled.1.2 (step H) hrem hqnH hstep hremLen hfcap
      let tail := run q fuel canceled.1.2
      have hip : price model tail.2≤10000000*(fuel+1)*model.rat (width (fuel+1) H) :=
        hi.trans (Nat.mul_le_mul_left (10000000*(fuel+1)) (model.monotone (next_width fuel H)))
      have htail := bounded_heights q fuel canceled.1.2 (step H) hqnH hrem hql hstep hfcap
      have htailq : HasHeight tail.1.1 (16105*step H+9665) := htail.1
      have htailr : HasHeight tail.1.2 (16105*step H+9665) := htail.2
      have htlen := lengths q fuel canceled.1.2 hqn hqm
      have htql : tail.1.1.length≤4 := htlen.1.trans hremLen
      have htrl : tail.1.2.length≤4 := htlen.2.trans hremLen
      let added := PlayerSpecificDenseExecution.add canceled.1.1 tail.1.1
      let quotient := PlayerSpecificDenseExecution.trim added.1
      have haddH : HasHeight added.1 (postHeight H) := by
        rw [PlayerSpecificDenseExecution.add_value]
        exact mono (add_height hterm htailq) (added_height H)
      have haddl : added.1.length≤4 := by
        rw [PlayerSpecificDenseExecution.add_value,PlayerSpecificDensePolynomial.add_length]
        exact max_le htermlen htql
      have ha := PlayerSpecificDenseOperationCost.add_cost model canceled.1.1 tail.1.1 (postHeight H) 4
        (mono hterm (post_ge H)) (mono htailq (tail_height H)) htermlen htql
      rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at ha
      have hap : price model added.2≤375000*model.rat (width (fuel+1) H) :=
        ha.trans (Nat.mul_le_mul_left 375000 (model.monotone (post_width (fuel+1) H)))
      have hqt := PlayerSpecificDenseOperationCost.trim_cost model added.1 (postHeight H) 4 haddH haddl
      rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at hqt
      have hqp : price model quotient.2≤375000*model.rat (width (fuel+1) H) :=
        hqt.trans (Nat.mul_le_mul_left 375000 (model.monotone (post_width (fuel+1) H)))
      have hpostw := post_width (fuel+1) H
      have hcopy := copy_cost model tail.1.2 (postHeight H) (width (fuel+1) H)
        (mono htailr (tail_height H)) htrl (by omega) hw
      have hc := PlayerSpecificCancellationTraceCost.run_cost model current.1 q H hcH hq hH hcl hql hp0 hq0
      have hcp : price model canceled.2≤5000000*model.rat (width (fuel+1) H) :=
        hc.trans (Nat.mul_le_mul_left 5000000 (model.monotone (cancellation_width (fuel+1) H)))
      change price model (current.2++header q (fuel+1) current.1++canceled.2++tail.2++added.2++quotient.2++
        copyRow tail.1.2++[.control 1])≤_
      simp only [price_append]
      nlinarith

theorem fixed_cost (model : RationalCostModel) (q p : Data) (H : ℕ)
    (hqn : Normalized q) (hqm : (semantics q).Monic) (hql : q.length≤4)
    (hp : HasHeight p H) (hq : HasHeight q H) (hH : 1≤H) (hpl : p.length≤4) :
    price model (run q p.length p).2≤50000000*model.rat (1000000^6*(H+1)) := by
  have h := run_cost model q p.length p H hqn hqm hql hp hq hH hpl hpl
  have hw := model.monotone (width_cap p.length H hpl)
  have hm := Nat.mul_le_mul_left (10000000*(p.length+1)) hw
  have hf := Nat.mul_le_mul_right (model.rat (1000000^6*(H+1)))
    (show 10000000*(p.length+1)≤50000000 by omega)
  exact (h.trans hm).trans hf

end Blotto.PlayerSpecificMonicDivisionTraceCost
