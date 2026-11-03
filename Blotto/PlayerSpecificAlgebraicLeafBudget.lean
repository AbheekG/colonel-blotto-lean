import Blotto.PlayerSpecificAlgebraicLeafValues

/-! The four-slot core loses no mass when its unused group slot is zero.
Direct proportional splitting and the optional fractional atom preserve
the full budget, including coordinates outside every terminal group. -/
namespace Blotto.PlayerSpecificAlgebraicLeafBudget
open PlayerSpecificAlgebraicLeafAssignments PlayerSpecificAlgebraicLeafValues
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem uniform_sum {m : ℕ} (y : Allocation 4) (hm : m=2 ∨ m=3) (hz : m=2 → y 2=0) :
    (∑ g : Fin m,y (slot g))=y 0+y 1+y 2 := by
  rcases hm with rfl|rfl
  · simp [slot,Fin.sum_univ_succ,hz rfl]
    rfl
  · simp [slot,Fin.sum_univ_succ,add_assoc]

theorem point_sum {N m : ℕ} (G : ProportionalGroups N m) (fractional : Option (Fin N)) (y : Allocation 4) :
    (∑ j,point G fractional y j)=(∑ g : Fin m,y (slot g))+
      match fractional with | none => 0 | some _ => y 3 := by
  classical
  cases fractional with
  | none =>
    simp only [PlayerSpecificAlgebraicLeafValues.point,add_zero,ProportionalGroups.split]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul,G.coefficient_sum,one_mul]
  | some k =>
    simp only [PlayerSpecificAlgebraicLeafValues.point]
    rw [Finset.sum_add_distrib]
    simp only [ProportionalGroups.split]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul,G.coefficient_sum,one_mul]
    simp

theorem point_fullBudget {N m : ℕ} (G : ProportionalGroups N m) (fractional : Option (Fin N))
    (y : Allocation 4) (B : ℝ) (hy : FullBudget B y) (hm : m=2 ∨ m=3)
    (hz : m=2 → y 2=0) (hn : fractional=none → y 3=0) : FullBudget B (point G fractional y) := by
  constructor
  · intro j
    have hs : 0 ≤ G.split (fun g => y (slot g)) j :=
      Finset.sum_nonneg (fun g _ => mul_nonneg (G.coefficient_nonnegative g j) (hy.1 (slot g)))
    change 0 ≤ G.split (fun g => y (slot g)) j+_
    apply add_nonneg hs
    cases fractional with
    | none => exact le_rfl
    | some k =>
      by_cases hj : j=k
      · simpa only [ite_eq_left hj] using hy.1 3
      · simp only [ite_eq_right hj,le_refl]
  · rw [point_sum,uniform_sum y hm hz]
    have hb : y 0+y 1+y 2+y 3=B := by
      simpa [Fin.sum_univ_succ,add_assoc] using hy.2
    cases fractional with
    | none => simpa only [hn rfl,add_zero] using hb
    | some k => exact hb

end Blotto.PlayerSpecificAlgebraicLeafBudget
