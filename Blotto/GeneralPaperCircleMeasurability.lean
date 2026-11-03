import Blotto.GeneralPaperCircleCanonicalLift

/-! The mathematical sorted-row reconstruction is measurable, including
coincident representative bids. This permits arbitrary whole-row laws. -/
namespace Blotto.GeneralPaperCircleMeasurability
open MeasureTheory Set
open GeneralPaperCircleCanonicalLift
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

theorem sorted_coordinate {R : ℕ} (a : Fin R) :
    Measurable (fun x : Fin R → ℝ => GeneralPaperCircleSortedComparison.sorted x a) := by
  have hMonotone (p : Equiv.Perm (Fin R)) :
      MeasurableSet {x : Fin R → ℝ | Monotone (x ∘ p)} := by
    have he : {x : Fin R → ℝ | Monotone (x ∘ p)} =
        ⋂ i : Fin R, ⋂ j : Fin R, {x | i ≤ j → x (p i) ≤ x (p j)} := by
      ext x
      simp [Monotone]
    rw [he]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases h : i ≤ j
    · simpa only [h, true_implies] using
        measurableSet_le (measurable_pi_apply (p i)) (measurable_pi_apply (p j))
    · simp only [h, false_implies, ofPred_true, MeasurableSet.univ]
  intro U hU
  have he : (fun x : Fin R → ℝ => GeneralPaperCircleSortedComparison.sorted x a) ⁻¹' U =
      ⋃ p : Equiv.Perm (Fin R),
        {x : Fin R → ℝ | Monotone (x ∘ p)} ∩ {x | x (p a) ∈ U} := by
    ext x
    constructor
    · intro hx
      exact mem_iUnion.mpr ⟨Tuple.sort x, Tuple.monotone_sort x, hx⟩
    · intro hx
      obtain ⟨p, hp, hxU⟩ := mem_iUnion.mp hx
      have hSort := Tuple.comp_sort_eq_comp_iff_monotone.mpr hp
      have ha := congrFun hSort a
      change x (p a) = GeneralPaperCircleSortedComparison.sorted x a at ha
      change GeneralPaperCircleSortedComparison.sorted x a ∈ U
      rw [← ha]
      exact hxU
  rw [he]
  exact MeasurableSet.iUnion fun p => (hMonotone p).inter ((measurable_pi_apply (p a)) hU)

theorem representatives {h R : ℕ} :
    Measurable (GeneralPaperCircleCanonicalLift.representatives : Allocation (h+R) → Allocation R) := by
  apply Measurable.of_eval
  intro a
  exact measurable_pi_apply (Fin.natAdd h a)

theorem row {h g : ℕ} (R W : ℕ) (hR : 0 < R) (hW : 0 < W)
    (weights : Fin g → ℕ) (shift : ℕ) :
    Measurable (GeneralPaperCircleCanonicalLift.row (h := h) R W hR hW weights · shift) := by
  apply Measurable.of_eval
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [GeneralPaperCircleCanonicalLift.row, GeneralPaperCircleHardBudget.reconstruct_kept, kept]
    exact measurable_pi_apply _
  · intro i
    simp only [GeneralPaperCircleCanonicalLift.row, GeneralPaperCircleHardBudget.reconstruct_light,
      GeneralPaperCircleHardBudget.bid]
    change Measurable (fun x : Allocation (h+R) =>
      ((GeneralPaperCircleHardBudget.lengths R weights i : ℝ)/W) *
        GeneralPaperCircleSortedComparison.sorted (GeneralPaperCircleCanonicalLift.representatives x) _)
    exact measurable_const.mul ((sorted_coordinate _).comp representatives)

end Blotto.GeneralPaperCircleMeasurability
