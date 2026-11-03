import Blotto.GeneralPaperSelectedCircularArc

/-! Exact selected-cell discrepancy for every integer circular interval.
The same two prefix errors give 1/S for wrapped intervals and for every
rotation. Uniform labels include repeated selected cells. -/
namespace Blotto.GeneralPaperSelectedArcDiscrepancy
open GeneralPaperSelectedShift GeneralPaperSelectedCircularArc GeneralPaperCircleFiniteAverage
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem average_sub {N : ℕ} (f g : Fin N → ℝ) : average (fun i => f i-g i)=average f-average g := by
  unfold average
  rw [Finset.sum_sub_distrib,sub_div]

theorem prefix_selected (D S : ℕ) (hD : 0<D) (hS : 0<S) (A : ℕ) :
    average (fun l:Fin S => prefixIndicator A (selected D S hD hS l))=
      (GeneralPaperSelectedPrefixCount.count D S hD hS A:ℝ)/S := by
  unfold prefixIndicator
  rw [average_indicator]
  rfl

theorem prefix_full (D : ℕ) (A : ℕ) (hA : A≤D) :
    average (fun c:Fin D => prefixIndicator A c)=(A:ℝ)/D := by
  unfold prefixIndicator
  rw [average_indicator,GeneralPaperQuantileRankCount.prefix_card,Nat.min_eq_right hA]

theorem prefix_error (D S : ℕ) (hD : 0<D) (hS : 0<S) (A : ℕ) (hA : A≤D) :
    -(1/(2*(S:ℝ)))≤average (fun l:Fin S => prefixIndicator A (selected D S hD hS l))-
        average (fun c:Fin D => prefixIndicator A c) ∧
      average (fun l:Fin S => prefixIndicator A (selected D S hD hS l))-
        average (fun c:Fin D => prefixIndicator A c)≤1/(2*(S:ℝ)) := by
  rw [prefix_selected,prefix_full D A hA]
  exact GeneralPaperSelectedPrefixCount.probability_bounds D S hD hS A hA

theorem arc_error (D S : ℕ) (hD : 0<D) (hS : 0<S) (start : Fin D) (L : ℕ) (hL : L≤D) :
    -(1/(S:ℝ))≤average (fun l:Fin S => if arc start L (selected D S hD hS l) then (1:ℝ) else 0)-
        average (fun c:Fin D => if arc start L c then (1:ℝ) else 0) ∧
      average (fun l:Fin S => if arc start L (selected D S hD hS l) then (1:ℝ) else 0)-
        average (fun c:Fin D => if arc start L c then (1:ℝ) else 0)≤1/(S:ℝ) := by
  have hA := prefix_error D S hD hS start.val start.isLt.le
  have hs : (S:ℝ)≠0 := by exact_mod_cast hS.ne'
  have hh : 1/(S:ℝ)=2*(1/(2*(S:ℝ))) := by field_simp
  by_cases hw:start.val+L≤D
  · have hB := prefix_error D S hD hS (start.val+L) hw
    simp_rw [arc_indicator start L hL,ite_eq_left hw]
    rw [average_sub,average_sub,hh]
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2]
  · have hB := prefix_error D S hD hS (start.val+L-D) (by have h := start.isLt;omega)
    simp_rw [arc_indicator start L hL,ite_eq_right hw]
    rw [average_sub,average_sub,average_add,average_add,
      GeneralPaperCircleCanonicalLift.average_const hS,GeneralPaperCircleCanonicalLift.average_const hD,hh]
    constructor <;> linarith only [hA.1,hA.2,hB.1,hB.2]

theorem rotated_error (D S : ℕ) (hD : 0<D) (hS : 0<S) (start : Fin D) (L : ℕ) (hL : L≤D) (shift : ℕ) :
    -(1/(S:ℝ))≤average (fun l:Fin S => if arc start L
          (GeneralPaperCircleCell.cell D hD shift (selected D S hD hS l).val) then (1:ℝ) else 0)-
        average (fun c:Fin D => if arc start L (GeneralPaperCircleCell.cell D hD shift c.val) then (1:ℝ) else 0) ∧
      average (fun l:Fin S => if arc start L
          (GeneralPaperCircleCell.cell D hD shift (selected D S hD hS l).val) then (1:ℝ) else 0)-
        average (fun c:Fin D => if arc start L (GeneralPaperCircleCell.cell D hD shift c.val) then (1:ℝ) else 0)≤1/(S:ℝ) := by
  simp_rw [rotated D hD start L shift]
  exact arc_error D S hD hS _ L hL

end Blotto.GeneralPaperSelectedArcDiscrepancy
