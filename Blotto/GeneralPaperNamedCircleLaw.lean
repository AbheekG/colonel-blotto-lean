import Blotto.GeneralPaperNamedCircleExecution

/-! Complete named rational draws agree pointwise with the selected circle
law after original-budget scaling. Original names come from retained native
arrays. Every realized allocation has the original hard at-most budget. -/
namespace Blotto.GeneralPaperNamedCircleLaw
open GeneralPaperNamedCircleExecution GeneralPaperLightFieldIndexEquiv
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem assemble_data {n R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (hR : 0<R) (c : ℚ) (prepared : Prepared state R) (chosen : FixedArrayTable state.light.size ℕ)
    (hBijective : Function.Bijective (mapping state)) :
    let light := (GeneralPaperNativeLightBids.run price index A hR prepared.coefficients prepared.sorted chosen).1
    (fun j => ((assemble price index A state hR c prepared chosen).1.read j:ℝ))=
      scaleAllocation (c:ℝ) (GeneralPaperFieldRelabel.allocation (Equiv.ofBijective (mapping state) hBijective).symm
        (Fin.addCases (fun j => (prepared.kept.read j:ℝ)) (fun j => (light.read j:ℝ)))) := by
  dsimp only
  change (fun j => ((GeneralPaperRationalOutputScale.run price index A c _).1.read j:ℝ))=_
  rw [GeneralPaperRationalOutputScale.real_data,GeneralPaperOriginalScatterLaw.data index A state _ _ hBijective]

theorem assemble_feasible {n R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (hR : 0<R) (c : ℚ) (hc : 0≤c) (prepared : Prepared state R) (chosen : FixedArrayTable state.light.size ℕ)
    (hBijective : Function.Bijective (mapping state)) (B : ℝ)
    (h : Feasible B (Fin.addCases (fun j => (prepared.kept.read j:ℝ))
      (fun j => ((GeneralPaperNativeLightBids.run price index A hR prepared.coefficients prepared.sorted chosen).1.read j:ℝ)))) :
    Feasible ((c:ℝ)*B) (fun j => ((assemble price index A state hR c prepared chosen).1.read j:ℝ)) := by
  rw [assemble_data price index A state hR c prepared chosen hBijective]
  apply scaleAllocation_feasible (by exact_mod_cast hc)
  exact (GeneralPaperFieldRelabel.feasible_iff (Equiv.ofBijective (mapping state) hBijective).symm B _).mpr h

theorem draw_data {n R : ℕ} (model : RationalCostModel) (W S : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (hR : 0<R) (hW : 0<W) (hS : 0<S) (c : ℚ) (kept : FixedArrayTable state.heavy.size ℚ)
    (row : FixedArrayTable R ℚ) (weights : FixedArrayTable state.light.size ℕ)
    (hs : ∑ j,weights.read j=W) (hBijective : Function.Bijective (mapping state)) (l : Fin S) :
    (fun j => ((drawArithmetic model W S state hR c
      (prepare (fun _ => 1) (fun _ => 1) 1 W state kept row weights).1 l).1.read j:ℝ))=
      scaleAllocation (c:ℝ) (GeneralPaperFieldRelabel.allocation (Equiv.ofBijective (mapping state) hBijective).symm
        (GeneralPaperCircleHardBudget.reconstruct R W hR hW weights.read (fun j => (kept.read j:ℝ))
          (GeneralPaperCircleSortedComparison.sorted (fun a => (row.read a:ℝ)))
          (GeneralPaperSelectedShift.selected (R*W) S (Nat.mul_pos hR hW) hS l).val)) := by
  change (fun j => ((assemble (fun _ => 1) (fun _ => 1) 1 state hR c _ _).1.read j:ℝ))=_
  rw [assemble_data _ _ _ _ _ _ _ _ hBijective]
  have he := funext (GeneralPaperNativeRationalCircleLaw.data model (fun _ => 1) (fun _ => 1) 1 W S hR hW hS l weights hs row)
  change scaleAllocation (c:ℝ) (GeneralPaperFieldRelabel.allocation _ (Fin.addCases _
    (fun j => (((GeneralPaperNativeLightBids.run (fun _ => 1) (fun _ => 1) 1 hR
      (GeneralPaperCircleRationalCoefficients.run (fun _ => 1) (fun _ => 1) 1 R W weights).1
      (GeneralPaperNativeSortedRows.one (fun _ => 1) (fun _ => 1) 1 row).1
      (GeneralPaperNativeChoiceArray.draw model R W S l.val
        (GeneralPaperNativeChoiceArray.prepare (fun _ => 1) 1 R weights).1).1).1.read j):ℝ))))=_
  rw [he]
  rfl

theorem draw_feasible {n R : ℕ} (model : RationalCostModel) (W S : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (hR : 0<R) (hW : 0<W) (hS : 0<S) (c : ℚ) (hc : 0≤c) (kept : FixedArrayTable state.heavy.size ℚ)
    (row : FixedArrayTable R ℚ) (weights : FixedArrayTable state.light.size ℕ)
    (hs : ∑ j,weights.read j=W) (hBijective : Function.Bijective (mapping state)) (l : Fin S) (B : ℝ)
    (hRow : Feasible B (Fin.addCases (fun j => (kept.read j:ℝ)) (fun a => (row.read a:ℝ)))) :
    Feasible ((c:ℝ)*B) (fun j => ((drawArithmetic model W S state hR c
      (prepare (fun _ => 1) (fun _ => 1) 1 W state kept row weights).1 l).1.read j:ℝ)) := by
  rw [draw_data model W S state hR hW hS c kept row weights hs hBijective l]
  apply scaleAllocation_feasible (by exact_mod_cast hc)
  apply (GeneralPaperFieldRelabel.feasible_iff (Equiv.ofBijective (mapping state) hBijective).symm B _).mpr
  exact GeneralPaperCircleSortedComparison.reconstruct_feasible R W hR hW weights.read hs
    (fun j => (kept.read j:ℝ)) (fun a => (row.read a:ℝ)) B hRow _

theorem draw_scaled_data {n R : ℕ} (model : RationalCostModel) (W S : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (hR : 0<R) (hW : 0<W) (hS : 0<S) (c : ℚ) (hc : 0<c) (kept : FixedArrayTable state.heavy.size ℚ)
    (row : FixedArrayTable R ℚ) (weights : FixedArrayTable state.light.size ℕ)
    (hs : ∑ j,weights.read j=W) (hBijective : Function.Bijective (mapping state)) (l : Fin S) :
    (fun j => ((drawArithmetic model W S state hR c
      (prepare (fun _ => 1) (fun _ => 1) 1 W state kept row weights).1 l).1.read j:ℝ))=
      GeneralPaperFieldRelabel.allocation (Equiv.ofBijective (mapping state) hBijective).symm
        (GeneralPaperCircleHardBudget.reconstruct R W hR hW weights.read
          (scaleAllocation (c:ℝ) (fun j => (kept.read j:ℝ)))
          (GeneralPaperCircleSortedComparison.sorted (fun a => (c:ℝ)*(row.read a:ℝ)))
          (GeneralPaperSelectedShift.selected (R*W) S (Nat.mul_pos hR hW) hS l).val) := by
  rw [GeneralPaperCircleSortedScale.reconstructed_scale R W hR hW weights.read
    (fun j => (kept.read j:ℝ)) (fun a => (row.read a:ℝ)) (c:ℝ) (by exact_mod_cast hc)]
  exact draw_data model W S state hR hW hS c kept row weights hs hBijective l

theorem original_draw_feasible {n R : ℕ} (bits : Bool) (model : RationalCostModel) (V k W S : ℕ)
    (input : FixedArrayTable n ℚ) (hR : 0<R) (hW : 0<W) (hS : 0<S) (c : ℚ) (hc : 0≤c)
    (kept : FixedArrayTable (GeneralPaperOriginalValueReduction.run bits model V k input).1.classified.heavy.size ℚ)
    (row : FixedArrayTable R ℚ)
    (weights : FixedArrayTable (GeneralPaperOriginalValueReduction.run bits model V k input).1.classified.light.size ℕ)
    (hs : ∑ j,weights.read j=W) (l : Fin S) (B : ℝ)
    (hRow : Feasible B (Fin.addCases (fun j => (kept.read j:ℝ)) (fun a => (row.read a:ℝ)))) :
    Feasible ((c:ℝ)*B) (fun j => ((drawArithmetic model W S
      (GeneralPaperOriginalValueReduction.run bits model V k input).1.classified hR c
      (prepare (fun _ => 1) (fun _ => 1) 1 W
        (GeneralPaperOriginalValueReduction.run bits model V k input).1.classified kept row weights).1 l).1.read j:ℝ)) :=
  draw_feasible model W S _ hR hW hS c hc kept row weights hs (original_bijective bits model V k input) l B hRow

end Blotto.GeneralPaperNamedCircleLaw
