import Blotto.GeneralPaperNativeChoiceArray

/-! Native stored sort, coefficients, selected sweep array and rational
products join the exact circle-law light bids. Hard at-most budgets follow
for the whole retained-plus-light row, without supplied sorting or indices.
Original-field scatter/scale and final priced sampler wiring remain open. -/
namespace Blotto.GeneralPaperNativeRationalCircleLaw
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem data {g R : ℕ} (model : RationalCostModel) (price index : ℕ → ℕ) (A W S : ℕ)
    (hR : 0<R) (hW : 0<W) (hS : 0<S) (l : Fin S) (weights : FixedArrayTable g ℕ)
    (hs : ∑ j,weights.read j=W) (row : FixedArrayTable R ℚ) (j : Fin g) :
    (((GeneralPaperNativeLightBids.run price index A hR
        (GeneralPaperCircleRationalCoefficients.run price index A R W weights).1
        (GeneralPaperNativeSortedRows.one price index A row).1
        (GeneralPaperNativeChoiceArray.draw model R W S l.val
          (GeneralPaperNativeChoiceArray.prepare price A R weights).1).1).1.read j):ℝ)=
      GeneralPaperCircleHardBudget.bid R W hR hW weights.read
        (GeneralPaperCircleSortedComparison.sorted (fun a => (row.read a:ℝ)))
        (GeneralPaperSelectedShift.selected (R*W) S (Nat.mul_pos hR hW) hS l).val j := by
  rw [GeneralPaperNativeLightBids.data,FixedArrayTable.read_ofFn,
    GeneralPaperNativeChoiceArray.selected_data model price A R W S hR hW hS l weights hs,FixedArrayTable.read_ofFn]
  rw [GeneralPaperNativeLightBids.read_valid]
  simp only [Rat.cast_mul]
  rw [GeneralPaperCircleRationalCoefficients.real_data,GeneralPaperNativeSortedRows.one_real]
  rfl

theorem feasible {h g R : ℕ} (model : RationalCostModel) (price index : ℕ → ℕ) (A W S : ℕ)
    (hR : 0<R) (hW : 0<W) (hS : 0<S) (l : Fin S) (weights : FixedArrayTable g ℕ)
    (hs : ∑ j,weights.read j=W) (kept : FixedArrayTable h ℚ) (row : FixedArrayTable R ℚ) (B : ℝ)
    (hRow : Feasible B (Fin.addCases (fun j => (kept.read j:ℝ)) (fun a => (row.read a:ℝ)))) :
    let bids := (GeneralPaperNativeLightBids.run price index A hR
      (GeneralPaperCircleRationalCoefficients.run price index A R W weights).1
      (GeneralPaperNativeSortedRows.one price index A row).1
      (GeneralPaperNativeChoiceArray.draw model R W S l.val (GeneralPaperNativeChoiceArray.prepare price A R weights).1).1).1
    Feasible B (Fin.addCases (fun j => (kept.read j:ℝ)) (fun j => (bids.read j:ℝ))) := by
  have he := funext (data model price index A W S hR hW hS l weights hs row)
  dsimp only
  rw [he]
  exact GeneralPaperCircleSortedComparison.reconstruct_feasible R W hR hW weights.read hs
    (fun j => (kept.read j:ℝ)) (fun a => (row.read a:ℝ)) B hRow _

theorem height {g R : ℕ} (model : RationalCostModel) (price index : ℕ → ℕ) (A W S H : ℕ)
    (hR : 0<R) (_hW : 0<W) (_hS : 0<S) (l : Fin S) (weights : FixedArrayTable g ℕ)
    (hw : ∀ j,weights.read j≤W) (row : FixedArrayTable R ℚ) (hRow : ∀ a,RationalHeight (row.read a) H) (j : Fin g) :
    RationalHeight
      ((GeneralPaperNativeLightBids.run price index A hR
        (GeneralPaperCircleRationalCoefficients.run price index A R W weights).1
        (GeneralPaperNativeSortedRows.one price index A row).1
        (GeneralPaperNativeChoiceArray.draw model R W S l.val (GeneralPaperNativeChoiceArray.prepare price A R weights).1).1).1.read j)
      (binaryWordWidth R+2*binaryWordWidth W+H) := by
  apply GeneralPaperNativeLightBids.height
  · intro a
    rw [GeneralPaperCircleRationalCoefficients.data,FixedArrayTable.read_ofFn]
    exact GeneralPaperCircleRationalCoefficients.ratio_height R W _ (hw a)
  · intro a
    rw [GeneralPaperNativeSortedRows.one_data,FixedArrayTable.read_ofFn]
    exact hRow _

end Blotto.GeneralPaperNativeRationalCircleLaw
