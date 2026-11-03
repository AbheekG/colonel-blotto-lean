import Blotto.OverlapLaw

/-! A normalized finite description of the exact gluing law. Zero-weight
entries use a fixed budget row so even unused slots have safe endpoints. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators

noncomputable def budgetRow (B : ℝ) : Allocation 4 := ![B, 0, 0, 0]

theorem budgetRow_fullBudget {B : ℝ} (hB : 0 ≤ B) : FullBudget B (budgetRow B) := by
  constructor
  · intro j
    fin_cases j
    · exact hB
    all_goals exact le_rfl
  · simp [budgetRow, Fin.sum_univ_succ]

namespace OverlapGluing

noncomputable def safeP {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h) : Allocation 4 :=
  if 0 < G.weight i j then (G.curve i j).value (G.lower i j) else budgetRow B

noncomputable def safeQ {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h) : Allocation 4 :=
  if 0 < G.weight i j then (G.curve i j).value (G.upper i j) else budgetRow B

theorem safe_contribution {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) (i : Fin k) (j : Fin h) :
    ENNReal.ofReal (G.weight i j) • (segmentLaw (G.safeP B i j) (G.safeQ B i j) : Measure (Allocation 4)) =
      ENNReal.ofReal (G.weight i j) •
        (segmentLaw ((G.curve i j).value (G.lower i j)) ((G.curve i j).value (G.upper i j)) : Measure (Allocation 4)) := by
  by_cases hp : 0 < G.weight i j
  · rw [safeP, safeQ, ite_eq_left hp, ite_eq_left hp]
  · have hz : G.weight i j = 0 := le_antisymm (le_of_not_gt hp) (G.weight_nonnegative i j)
    simp [hz]

noncomputable def descriptor {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) : SegmentLottery 4 (k * h) where
  weight := fun r => G.weight (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2
  P := fun r => G.safeP B (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2
  Q := fun r => G.safeQ B (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2
  nonnegative := fun r => G.weight_nonnegative _ _
  mass := by
    have he := Equiv.sum_comp (finProdFinEquiv.symm : Fin (k * h) ≃ Fin k × Fin h)
      (fun r => G.weight r.1 r.2)
    rw [he]
    simpa only [← Finset.univ_product_univ, Finset.sum_product] using G.weights_mass

/-- The descriptor represents the same actual conditional allocation law. -/
theorem descriptor_law {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) :
    ((G.descriptor B).law : Measure (Allocation 4)) =
      (G.auxiliary.allocationLaw : Measure (Allocation 4)) := by
  rw [SegmentLottery.law_measure, G.allocation_measure]
  simp only [Measure.sum_fintype]
  have he := Equiv.sum_comp (finProdFinEquiv.symm : Fin (k * h) ≃ Fin k × Fin h)
    (fun r => ENNReal.ofReal (G.weight r.1 r.2) •
      (segmentLaw (G.safeP B r.1 r.2) (G.safeQ B r.1 r.2) : Measure (Allocation 4)))
  change (∑ r : Fin (k * h), ENNReal.ofReal (G.weight (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2) •
    (segmentLaw (G.safeP B (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2)
      (G.safeQ B (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2) : Measure (Allocation 4))) = _
  rw [he, ← Finset.univ_product_univ, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact G.safe_contribution B i j

theorem positive_sources {k h : ℕ} (G : OverlapGluing k h) {i : Fin k} {j : Fin h}
    (hw : 0 < G.weight i j) : 0 < G.first.weight i ∧ 0 < G.second.weight j := by
  constructor
  · by_contra h
    have hz : G.first.weight i = 0 := le_antisymm (le_of_not_gt h) (G.first.nonnegative i)
    simp [weight, density, SegmentLottery.conditionalWeight, hz] at hw
  · by_contra h
    have hz : G.second.weight j = 0 := le_antisymm (le_of_not_gt h) (G.second.nonnegative j)
    simp [weight, density, hz] at hw

theorem positive_overlap {k h : ℕ} (G : OverlapGluing k h) {i : Fin k} {j : Fin h}
    (hw : 0 < G.weight i j) : G.lower i j < G.upper i j := by
  by_contra h
  have hz : G.upper i j - G.lower i j ≤ 0 := sub_nonpos.mpr (le_of_not_gt h)
  simp [weight, max_eq_right hz] at hw

/-- Positive overlap entries are contained in the Cartesian product of the
positive source slots. Thus seven-by-seven sources yield at most 49 entries. -/
theorem descriptor_positive_bound {k h : ℕ} (G : OverlapGluing k h) (B : ℝ) :
    (G.descriptor B).positiveSlots.card ≤ G.first.positiveSlots.card * G.second.positiveSlots.card := by
  classical
  have hs : (G.descriptor B).positiveSlots ⊆
      (G.first.positiveSlots ×ˢ G.second.positiveSlots).image finProdFinEquiv := by
    intro r hr
    have hw : 0 < G.weight (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2 :=
      (Finset.mem_filter.mp hr).2
    have hp := G.positive_sources hw
    apply Finset.mem_image.mpr
    refine ⟨finProdFinEquiv.symm r, ?_, finProdFinEquiv.apply_symm_apply r⟩
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ finProdFinEquiv.injective, Finset.card_product] at hc
  exact hc

end OverlapGluing
end Blotto
