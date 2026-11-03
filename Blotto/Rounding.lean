import Blotto.Model

/-! Manuscript §2.1.2: one pairwise randomized resource-rounding step.
Both branches preserve resources and close at least one fractional coordinate;
the two-point lottery preserves both conditional expectations exactly. -/

namespace Blotto

structure RoundingPair where
  lengthI : ℝ
  lengthJ : ℝ
  resourceI : ℝ
  resourceJ : ℝ
  interiorI : 0 < resourceI ∧ resourceI < lengthI
  interiorJ : 0 < resourceJ ∧ resourceJ < lengthJ

namespace RoundingPair

noncomputable def total (r : RoundingPair) : ℝ := r.resourceI + r.resourceJ
noncomputable def lower (r : RoundingPair) : ℝ := max 0 (r.total - r.lengthJ)
noncomputable def upper (r : RoundingPair) : ℝ := min r.lengthI r.total
noncomputable def probability (r : RoundingPair) : ℝ :=
  (r.resourceI - r.lower) / (r.upper - r.lower)

theorem lower_lt_resource (r : RoundingPair) : r.lower < r.resourceI := by
  simp only [lower, max_lt_iff, total]
  constructor <;> linarith [r.interiorI.1, r.interiorJ.2]

theorem resource_lt_upper (r : RoundingPair) : r.resourceI < r.upper := by
  simp only [upper, lt_min_iff, total]
  constructor <;> linarith [r.interiorI.2, r.interiorJ.1]

theorem lower_lt_upper (r : RoundingPair) : r.lower < r.upper :=
  lt_trans r.lower_lt_resource r.resource_lt_upper

theorem probability_pos (r : RoundingPair) : 0 < r.probability :=
  div_pos (sub_pos.mpr r.lower_lt_resource) (sub_pos.mpr r.lower_lt_upper)

theorem probability_lt_one (r : RoundingPair) : r.probability < 1 := by
  apply (div_lt_one (sub_pos.mpr r.lower_lt_upper)).mpr
  linarith [r.resource_lt_upper]

/-- Both actual output rows lie in the original two-coordinate box. -/
theorem branch_feasible (r : RoundingPair) {z : ℝ} (hz : z = r.lower ∨ z = r.upper) :
    0 ≤ z ∧ z ≤ r.lengthI ∧ 0 ≤ r.total - z ∧ r.total - z ≤ r.lengthJ := by
  have hL0 : 0 ≤ r.lower := le_max_left _ _
  have hLL : r.total - r.lengthJ ≤ r.lower := le_max_right _ _
  have hUI : r.upper ≤ r.lengthI := min_le_left _ _
  have hUT : r.upper ≤ r.total := min_le_right _ _
  have hLU := le_of_lt r.lower_lt_upper
  rcases hz with rfl | rfl <;> constructor
  · exact hL0
  · exact ⟨by linarith, by linarith, by linarith⟩
  · linarith
  · exact ⟨hUI, by linarith, by linarith⟩

/-- In each branch at least one of the selected coordinates becomes integral. -/
theorem branch_endpoint (r : RoundingPair) {z : ℝ} (hz : z = r.lower ∨ z = r.upper) :
    z = 0 ∨ z = r.lengthI ∨ r.total - z = 0 ∨ r.total - z = r.lengthJ := by
  rcases hz with rfl | rfl
  · unfold lower
    rcases le_total 0 (r.total - r.lengthJ) with h | h
    · rw [max_eq_right h]
      right; right; right; ring
    · rw [max_eq_left h]
      exact Or.inl rfl
  · unfold upper
    rcases le_total r.lengthI r.total with h | h
    · rw [min_eq_left h]
      exact Or.inr (Or.inl rfl)
    · rw [min_eq_right h]
      right; right; left; ring

theorem branch_sum (r : RoundingPair) (z : ℝ) :
    z + (r.total - z) = r.resourceI + r.resourceJ := by
  unfold total
  ring

theorem expected_resourceI (r : RoundingPair) :
    r.probability * r.upper + (1 - r.probability) * r.lower = r.resourceI := by
  unfold probability
  field_simp [ne_of_gt (sub_pos.mpr r.lower_lt_upper)]
  ring

theorem expected_resourceJ (r : RoundingPair) :
    r.probability * (r.total - r.upper) +
      (1 - r.probability) * (r.total - r.lower) = r.resourceJ := by
  have he := r.expected_resourceI
  unfold total at *
  nlinarith

/-- Averaging any affine marginal mixture coefficient recovers its old value. -/
theorem expected_mixture (r : RoundingPair) (C D : ℝ) :
    r.probability * (C + D * r.upper) +
      (1 - r.probability) * (C + D * r.lower) = C + D * r.resourceI := by
  calc
    _ = C + D * (r.probability * r.upper + (1 - r.probability) * r.lower) := by ring
    _ = _ := by rw [r.expected_resourceI]

end RoundingPair

/-- The grouping argument's decisive four-group contradiction. -/
theorem cannot_have_four_groups {B g1 g2 g3 g4 : ℝ}
    (h12 : B < g1 + g2) (h34 : B < g3 + g4)
    (hsum : g1 + g2 + g3 + g4 ≤ 2 * B) : False := by
  linarith

end Blotto
