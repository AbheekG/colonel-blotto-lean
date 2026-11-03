import Blotto.GeneralPaperCircleMetadataSweep

/-! Native real-RAM control draw: compute the selected shift once and
sweep the retained ordered metadata once. The returned indices agree with
the selected-cell law. Sorted-row lookup, rational bids/original-field
scatter, full draw bit prices and final sampler wiring remain separate. -/
namespace Blotto.GeneralPaperNativeCircleControlDraw
open GeneralPaperCircleCell
set_option autoImplicit false
set_option maxHeartbeats 2000000

def run (model : RationalCostModel) (R W S l : ℕ) (arcs : List (ℕ×ℕ)) : GeneralPaperCircleCursorSweep.Result × ℕ :=
  let shifted := GeneralPaperNativeShiftExecution.run false model 1 (R*W) S l
  let swept := GeneralPaperCircleCursorSweep.run R W shifted.1.cell arcs 0 (2*W)
  (swept,shifted.2+swept.work+16)

theorem data (model : RationalCostModel) (R W S : ℕ) (hR : 0<R) (hW : 0<W) (hS : 0<S) (l : Fin S)
    (arcs : List (ℕ×ℕ)) :
    (run model R W S l.val arcs).1=GeneralPaperCircleCursorSweep.run R W
      (GeneralPaperSelectedShift.selected (R*W) S (Nat.mul_pos hR hW) hS l).val arcs 0 (2*W) := by
  unfold run
  dsimp only
  rw [GeneralPaperNativeShiftExecution.selected_data false model 1 (R*W) S (Nat.mul_pos hR hW) hS l]

theorem prepared_correct (model : RationalCostModel) (price : ℕ → ℕ) (A R W S : ℕ)
    (hR : 0<R) (hW : 0<W) (hS : 0<S) (l : Fin S) (weights : List ℕ) (hs : weights.sum=W) :
    let arcs := (GeneralPaperCircleArcMetadata.run price A R weights 0).1.arcs
    (run model R W S l.val arcs).1.indices=arcs.map (fun arc =>
      (choice R W hR hW (cell (R*W) (Nat.mul_pos hR hW)
        (GeneralPaperSelectedShift.selected (R*W) S (Nat.mul_pos hR hW) hS l).val arc.1) arc.2).val) := by
  dsimp only
  rw [data model R W S hR hW hS l]
  have h := GeneralPaperCircleCursorSweep.correct R W
    (GeneralPaperSelectedShift.selected (R*W) S (Nat.mul_pos hR hW) hS l).val hR hW
    (GeneralPaperSelectedShift.selected (R*W) S (Nat.mul_pos hR hW) hS l).isLt
    (GeneralPaperCircleArcMetadata.run price A R weights 0).1.arcs 0 (2*W) (by omega) (by omega)
    (fun arc hm => by
      have h := GeneralPaperCircleArcMetadata.ranges price A R weights 0 arc hm
      simpa only [GeneralPaperCircleArcMetadata.total,hs,Nat.zero_add] using h)
    (GeneralPaperCircleArcMetadata.ordered price A R weights 0)
    (fun arc _ => by simp only [Nat.zero_mul];omega)
  exact h.1

theorem arithmetic_work (model : RationalCostModel) (price : ℕ → ℕ) (A R W S l : ℕ)
    (hR : 0<R) (hW : 0<W) (hS : 0<S) (hl : l<S) (weights : List ℕ) (hs : weights.sum=W) :
    (run model R W S l (GeneralPaperCircleArcMetadata.run price A R weights 0).1.arcs).2≤
      1024*(binaryWordWidth (R*W)+1)+24*R+36*weights.length+20 := by
  have hShift := GeneralPaperNativeShiftPrice.arithmetic_work model (R*W) S l (Nat.mul_pos hR hW) hS hl
  have ht := GeneralPaperNativeShiftExecution.cell_bound false model 1 (R*W) S l (Nat.mul_pos hR hW) hS hl
  have hSweep := GeneralPaperCircleMetadataSweep.work price A R W
    (GeneralPaperNativeShiftExecution.run false model 1 (R*W) S l).1.cell hR hW ht weights hs
  change (GeneralPaperNativeShiftExecution.run false model 1 (R*W) S l).2+
    (GeneralPaperCircleCursorSweep.run R W (GeneralPaperNativeShiftExecution.run false model 1 (R*W) S l).1.cell
      (GeneralPaperCircleArcMetadata.run price A R weights 0).1.arcs 0 (2*W)).work+16≤_
  omega

end Blotto.GeneralPaperNativeCircleControlDraw
