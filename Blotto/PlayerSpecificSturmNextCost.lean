import Blotto.PlayerSpecificSturmCopyCost

/-! Signed remainders charge actual division, negation, trimming and copies.
Negation preserves coefficient heights, so Euclidean widths suffice. -/
namespace Blotto.PlayerSpecificSturmNextCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificSturmExecution PlayerSpecificEuclideanBudget
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem bounds (p q : Data) (H : ℕ) (hp : HasHeight p H) (hq : HasHeight q H)
    (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) :
    HasHeight (next p q).1 (step H) ∧ (next p q).1.length≤4 := by
  rw [next_value]
  have h:=PlayerSpecificSturmHeights.next_bounds p q H hp hq hH hpl hql
  rw [PlayerSpecificDivisionHeights.linear] at h
  exact h

theorem next_cost (model : RationalCostModel) (fuel : ℕ) (p q : Data) (H : ℕ)
    (hp : HasHeight p H) (hq : HasHeight q H) (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) :
    price model (next p q).2≤110000000*model.rat (width fuel H) := by
  let divided := PlayerSpecificDivisionExecution.run p q
  let negated := PlayerSpecificDenseExecution.scale (-1) divided.1.2
  let normalized := PlayerSpecificDenseExecution.trim negated.1
  have hDH : HasHeight divided.1.2 (step H) := (PlayerSpecificDivisionExecution.heights p q H hp hq hH hpl hql).2
  have hDl : divided.1.2.length≤4 := (PlayerSpecificDivisionExecution.lengths p q).2.trans hpl
  have hNH : HasHeight negated.1 (step H) := by
    rw [PlayerSpecificDenseExecution.scale_value]
    exact negative_height hDH
  have hNl : negated.1.length≤4 := by rw [PlayerSpecificDenseExecution.scale_value,scale_length]; exact hDl
  have hRH : HasHeight normalized.1 (step H) := by rw [PlayerSpecificDenseExecution.trim_value]; exact trim_height hNH
  have hRl : normalized.1.length≤4 := by rw [PlayerSpecificDenseExecution.trim_value]; exact (trim_length _).trans hNl
  have hstep : 1≤step H := hH.trans (step_ge H)
  have hd := PlayerSpecificDivisionTraceCost.run_cost model p q H hp hq hH hpl hql
  have hdp := hd.trans (Nat.mul_le_mul_left 100000000 (model.monotone (division_width fuel H)))
  have hw : 40*step H+64≤width fuel H := by
    have hm:=post_width fuel H
    have hs:=step_le_post H
    unfold PlayerSpecificCompositeTraceFits.width PlayerSpecificCompositeTraceFits.height at hm
    nlinarith
  have hs := PlayerSpecificDenseOperationCost.scale_cost model (-1) divided.1.2 (step H) 4
    (one_height.neg.mono hstep) hDH hDl
  have ht := PlayerSpecificDenseOperationCost.trim_cost model negated.1 (step H) 4 hNH hNl
  rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at hs ht
  have hsp:=hs.trans (Nat.mul_le_mul_left 375000 (model.monotone hw))
  have htp:=ht.trans (Nat.mul_le_mul_left 375000 (model.monotone hw))
  have hW : 6≤width fuel H := (by decide : 6≤32).trans (width_large fuel H)
  have hc:=PlayerSpecificMonicDivisionBudget.copy_cost model normalized.1 (step H) (width fuel H) hRH hRl
    (by omega) hW
  have hf:=PlayerSpecificMonicDivisionBudget.control_cost model 1 (width fuel H) (by omega) hW
  change price model (divided.2++negated.2++normalized.2++copyRow normalized.1++[.control 1])≤_
  simp only [price_append]
  nlinarith

end Blotto.PlayerSpecificSturmNextCost
