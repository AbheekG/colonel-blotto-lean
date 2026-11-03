import Blotto.GeneralPaperContinuousUniformCells

/-! The geometric continuous-rotation lift and its exact full-cell law.
The shift and the complete reduced allocation are independent. Essential
arc minima use the positive-overlap finite-range characterization. -/
namespace Blotto.GeneralPaperContinuousCircleLaw
open MeasureTheory Set
open GeneralPaperCircleCanonicalLift GeneralPaperCircleCell
open GeneralPaperContinuousArcMinimum GeneralPaperContinuousUniformCells
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

noncomputable def row {h g : ℕ} (R W : ℕ) (weights : Fin g → ℕ)
    (x : Allocation (h+R)) (u : ℝ) : Allocation (h+g) :=
  Fin.addCases (kept x) (fun j => (weights j : ℝ)/W * minimum R W
    ((R*W : ℕ)*u + (GeneralPaperCircleArcPartition.before (GeneralPaperCircleHardBudget.lengths R weights) j.val : ℝ))
    (GeneralPaperCircleHardBudget.lengths R weights j)
    (GeneralPaperCircleSortedComparison.sorted (representatives x)))

theorem row_on_cell {h g : ℕ} (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (weights : Fin g → ℕ) (hp : ∀ j, 0 < weights j)
    (x : Allocation (h+R)) (u : ℝ) (s : Fin (R*W))
    (hu : (s.val : ℝ) < (R*W : ℕ)*u ∧ (R*W : ℕ)*u < (s.val : ℝ)+1) :
    row R W weights x u = GeneralPaperCircleCanonicalLift.row R W hR hW weights x s.val := by
  let tau := (R*W : ℕ)*u-(s.val : ℝ)
  have ht0 : 0 < tau := by dsimp only [tau]; linarith only [hu.1]
  have ht1 : tau < 1 := by dsimp only [tau]; linarith only [hu.2]
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [row, Fin.addCases_left, GeneralPaperCircleCanonicalLift.row,
      GeneralPaperCircleHardBudget.reconstruct_kept]
  · intro i
    simp only [row, Fin.addCases_right, GeneralPaperCircleCanonicalLift.row,
      GeneralPaperCircleHardBudget.reconstruct_light, GeneralPaperCircleHardBudget.bid]
    let p := GeneralPaperCircleArcPartition.before (GeneralPaperCircleHardBudget.lengths R weights) i.val
    have hStart : (R*W : ℕ)*u+(p : ℝ) = ((s.val+p : ℕ) : ℝ)+tau := by
      dsimp only [tau]
      push_cast
      ring
    change (weights i : ℝ)/W * minimum R W ((R*W : ℕ)*u+(p : ℝ))
      (GeneralPaperCircleHardBudget.lengths R weights i) _ = _
    rw [hStart]
    have hMinimum := unrolled_cell_minimum R W hR hW (s.val+p)
      (GeneralPaperCircleHardBudget.lengths R weights i) (Nat.mul_pos hR (hp i)) tau ht0 ht1
      (GeneralPaperCircleSortedComparison.sorted (representatives x))
      (GeneralPaperCircleSortedComparison.sorted_monotone (representatives x))
    rw [hMinimum]
    have hCell : cell (R*W) (Nat.mul_pos hR hW) (s.val+p) 0 =
        cell (R*W) (Nat.mul_pos hR hW) s.val p := by
      apply Fin.ext
      simp only [cell, Nat.add_zero]
    rw [hCell]
    simp only [GeneralPaperCircleHardBudget.lengths, Nat.cast_mul]
    ring

noncomputable def representative {h g : ℕ} (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (weights : Fin g → ℕ) (z : ℝ × Allocation (h+R)) : Allocation (h+g) :=
  GeneralPaperCircleCanonicalLift.row R W hR hW weights z.2 (index (R*W) (Nat.mul_pos hR hW) z.1).val

theorem measurable_representative {h g : ℕ} (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (weights : Fin g → ℕ) : Measurable (representative (h := h) R W hR hW weights) := by
  have hb : Measurable (fun z : Fin (R*W) × Allocation (h+R) =>
      GeneralPaperCircleCanonicalLift.row R W hR hW weights z.2 z.1.val) :=
    measurable_from_prod_countable_right (fun s => GeneralPaperCircleMeasurability.row R W hR hW weights s.val)
  exact hb.comp (((measurable_index (R*W) (Nat.mul_pos hR hW)).comp measurable_fst).prodMk measurable_snd)

theorem row_ae {h g : ℕ} (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (weights : Fin g → ℕ) (hp : ∀ j, 0 < weights j) :
    ∀ᵐ u ∂(unitUniform : Measure ℝ), ∀ x : Allocation (h+R),
      row R W weights x u = representative R W hR hW weights (u,x) := by
  filter_upwards [interior_ae (R*W) (Nat.mul_pos hR hW)] with u hu
  intro x
  exact row_on_cell R W hR hW weights hp x u _ hu

theorem row_product_ae {h g : ℕ} (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (weights : Fin g → ℕ) (hp : ∀ j, 0 < weights j) (P : Mixed (h+R)) :
    (fun z : ℝ × Allocation (h+R) => row R W weights z.2 z.1) =ᵐ[
      (unitUniform : Measure ℝ).prod (P : Measure (Allocation (h+R)))]
        representative R W hR hW weights := by
  have hPull := (Measure.quasiMeasurePreserving_fst (μ := (unitUniform : Measure ℝ))
    (ν := (P : Measure (Allocation (h+R))))).ae (row_ae (h := h) R W hR hW weights hp)
  exact hPull.mono (fun z hz => hz z.2)

theorem aemeasurable_row {h g : ℕ} (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (weights : Fin g → ℕ) (hp : ∀ j, 0 < weights j) (P : Mixed (h+R)) :
    AEMeasurable (fun z : ℝ × Allocation (h+R) => row R W weights z.2 z.1)
      ((unitUniform : Measure ℝ).prod (P : Measure (Allocation (h+R)))) :=
  (measurable_representative R W hR hW weights).aemeasurable.congr
    (row_product_ae R W hR hW weights hp P).symm

noncomputable def law {h g : ℕ} (R W : ℕ) (weights : Fin g → ℕ) (P : Mixed (h+R)) : Mixed (h+g) :=
  (RealUniformInputs.productLaw unitUniform P).map (fun z => row R W weights z.2 z.1)

theorem representative_law {h g : ℕ} (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (weights : Fin g → ℕ) (P : Mixed (h+R)) :
    (RealUniformInputs.productLaw unitUniform P).map (representative R W hR hW weights) =
      GeneralPaperMixedCircleLift.law R W hR hW weights P := by
  let D := R*W
  let hD : 0 < D := Nat.mul_pos hR hW
  let laws := fun s : Fin D => P.map (fun x => GeneralPaperCircleCanonicalLift.row R W hR hW weights x s.val)
  have hAve := averaged_laws D hD laws
  apply ProbabilityMeasure.toMeasure_injective
  change ((RealUniformInputs.productLaw unitUniform P).map (representative R W hR hW weights) :
    Measure (Allocation (h+g))) = (GeneralPaperUniformRowLaw.mixture hD laws : Measure (Allocation (h+g)))
  rw [← hAve]
  change Measure.map (representative R W hR hW weights)
    ((unitUniform : Measure ℝ).prod (P : Measure (Allocation (h+R)))) =
      (unitUniform : Measure ℝ).bind (fun u => (laws (index D hD u) : Measure (Allocation (h+g))))
  have hm : Measurable (fun u => (laws (index D hD u) : Measure (Allocation (h+g)))) :=
    (measurable_of_countable (fun s => (laws s : Measure (Allocation (h+g))))).comp (measurable_index D hD)
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_representative R W hR hW weights) hA,
    Measure.prod_apply (hA.preimage (measurable_representative R W hR hW weights)),
    Measure.bind_apply hA hm.aemeasurable]
  apply lintegral_congr
  intro u
  change (P : Measure (Allocation (h+R))) (Prod.mk u ⁻¹' representative R W hR hW weights ⁻¹' A) =
    Measure.map (fun x => GeneralPaperCircleCanonicalLift.row R W hR hW weights x (index D hD u).val)
      (P : Measure (Allocation (h+R))) A
  rw [Measure.map_apply (GeneralPaperCircleMeasurability.row R W hR hW weights (index D hD u).val) hA]
  rfl

theorem law_eq {h g : ℕ} (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (weights : Fin g → ℕ) (hp : ∀ j, 0 < weights j) (P : Mixed (h+R)) :
    law R W weights P = GeneralPaperMixedCircleLift.law R W hR hW weights P := by
  calc
    _ = (RealUniformInputs.productLaw unitUniform P).map (representative R W hR hW weights) := by
      apply ProbabilityMeasure.toMeasure_injective
      exact Measure.map_congr (row_product_ae R W hR hW weights hp P)
    _ = _ := representative_law R W hR hW weights P

theorem supported {h g : ℕ} (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (weights : Fin g → ℕ) (hp : ∀ j, 0 < weights j) (hs : ∑ j, weights j = W)
    (P : Mixed (h+R)) (B : ℝ) (hP : Supported B P) : Supported B (law R W weights P) := by
  rw [law_eq R W hR hW weights hp P]
  exact GeneralPaperMixedCircleLift.supported R W hR hW weights hs P B hP

end Blotto.GeneralPaperContinuousCircleLaw
