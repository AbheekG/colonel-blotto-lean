import Blotto.FourUniforms
import Blotto.Boxes

/-! Proportional splitting from a disjoint group partition. This module
proves actual marginal push-forwards and every output's budget. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators

structure ProportionalGroups (n m : ℕ) where
  length : Allocation n
  length_pos : ∀ i, 0 < length i
  members : Fin m → Finset (Fin n)
  disjoint : ∀ g h, g ≠ h → Disjoint (members g) (members h)
  total_pos : ∀ g, 0 < ∑ i ∈ members g, length i

namespace ProportionalGroups

noncomputable def total {n m : ℕ} (G : ProportionalGroups n m) (g : Fin m) : ℝ :=
  ∑ i ∈ G.members g, G.length i

noncomputable def coefficient {n m : ℕ} (G : ProportionalGroups n m) (g : Fin m) (i : Fin n) : ℝ :=
  if i ∈ G.members g then G.length i / G.total g else 0

noncomputable def split {n m : ℕ} (G : ProportionalGroups n m) (y : Allocation m) : Allocation n :=
  fun i => ∑ g, G.coefficient g i * y g

theorem coefficient_nonnegative {n m : ℕ} (G : ProportionalGroups n m) (g : Fin m) (i : Fin n) :
    0 ≤ G.coefficient g i := by
  unfold coefficient
  split_ifs
  · exact div_nonneg (le_of_lt (G.length_pos i)) (le_of_lt (G.total_pos g))
  · exact le_rfl

theorem coefficient_sum {n m : ℕ} (G : ProportionalGroups n m) (g : Fin m) : ∑ i, G.coefficient g i = 1 := by
  classical
  simp only [coefficient]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div]
  exact div_self (ne_of_gt (G.total_pos g))

theorem split_fullBudget {n m : ℕ} (G : ProportionalGroups n m) {B : ℝ} {y : Allocation m}
    (hy : FullBudget B y) : FullBudget B (G.split y) := by
  constructor
  · intro i
    exact Finset.sum_nonneg (fun g _ => mul_nonneg (G.coefficient_nonnegative g i) (hy.1 g))
  · unfold split
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, G.coefficient_sum, one_mul]
    exact hy.2

theorem split_group_coordinate {n m : ℕ} (G : ProportionalGroups n m) {i : Fin n} {g : Fin m}
    (hi : i ∈ G.members g) (y : Allocation m) : G.split y i = G.length i / G.total g * y g := by
  classical
  unfold split
  rw [Finset.sum_eq_single g]
  · simp [coefficient, hi]
  · intro h _ hh
    have hn : i ∉ G.members h := by
      intro hm
      exact (Finset.disjoint_left.mp (G.disjoint h g hh)) hm hi
    simp [coefficient, hn]
  · simp

theorem split_inactive_coordinate {n m : ℕ} (G : ProportionalGroups n m) {i : Fin n}
    (hi : ∀ g, i ∉ G.members g) (y : Allocation m) : G.split y i = 0 := by
  simp [split, coefficient, hi]

theorem measurable_split {n m : ℕ} (G : ProportionalGroups n m) : Measurable G.split := by
  apply Measurable.of_eval
  intro i
  exact Finset.measurable_sum _ (fun g _ => measurable_const.mul (measurable_pi_apply g))

noncomputable def splitLaw {n m : ℕ} (G : ProportionalGroups n m) (μ : Mixed m) : Mixed n := μ.map G.split

theorem splitLaw_fullBudget {n m : ℕ} (G : ProportionalGroups n m) {B : ℝ} (μ : Mixed m)
    (hμ : ∀ᵐ y ∂(μ : Measure (Allocation m)), FullBudget B y) :
    ∀ᵐ x ∂(G.splitLaw μ : Measure (Allocation n)), FullBudget B x := by
  change ∀ᵐ x ∂Measure.map G.split (μ : Measure (Allocation m)), FullBudget B x
  rw [ae_map_iff G.measurable_split.aemeasurable (measurable_fullBudget B)]
  exact hμ.mono fun _ hy => G.split_fullBudget hy

theorem splitLaw_marginal_group {n m : ℕ} (G : ProportionalGroups n m) (μ : Mixed m)
    {i : Fin n} {g : Fin m} (hi : i ∈ G.members g) :
    (marginal (G.splitLaw μ) i : Measure ℝ) =
      Measure.map (fun x => G.length i / G.total g * x) (marginal μ g : Measure ℝ) := by
  change Measure.map (fun x : Allocation n => x i) (Measure.map G.split (μ : Measure (Allocation m))) =
    Measure.map (fun x => G.length i / G.total g * x) (Measure.map (fun y : Allocation m => y g) (μ : Measure (Allocation m)))
  rw [Measure.map_map (measurable_pi_apply i) G.measurable_split,
    Measure.map_map (g := fun x : ℝ => G.length i / G.total g * x)
      (measurable_const.mul measurable_id) (measurable_pi_apply g)]
  congr 1
  funext y
  exact G.split_group_coordinate hi y

theorem splitLaw_uniform {n m : ℕ} (G : ProportionalGroups n m) (μ : Mixed m)
    (hμ : ∀ g, (marginal μ g : Measure ℝ) = uniformLaw (G.total g))
    {i : Fin n} {g : Fin m} (hi : i ∈ G.members g) :
    (marginal (G.splitLaw μ) i : Measure ℝ) = uniformLaw (G.length i) := by
  rw [G.splitLaw_marginal_group μ hi, hμ g]
  exact scale_uniformLaw (G.length_pos i) (G.total_pos g)

theorem splitLaw_inactive {n m : ℕ} (G : ProportionalGroups n m) (μ : Mixed m)
    {i : Fin n} (hi : ∀ g, i ∉ G.members g) :
    (marginal (G.splitLaw μ) i : Measure ℝ) = Measure.dirac 0 := by
  change Measure.map (fun x : Allocation n => x i) (Measure.map G.split (μ : Measure (Allocation m))) = _
  rw [Measure.map_map (measurable_pi_apply i) G.measurable_split]
  have he : (fun x : Allocation n => x i) ∘ G.split = fun _ : Allocation m => (0 : ℝ) :=
    funext (G.split_inactive_coordinate hi)
  rw [he, Measure.map_const, measure_univ, one_smul]

noncomputable def splitMixed {n m : ℕ} (G : ProportionalGroups n m) (pivot : Fin n)
    (y : Allocation (m + 1)) : Allocation n :=
  fun i => G.split (fun g => y g.castSucc) i + if i = pivot then y (Fin.last m) else 0

theorem splitMixed_pivot {n m : ℕ} (G : ProportionalGroups n m) (pivot : Fin n)
    (hp : ∀ g, pivot ∉ G.members g) (y : Allocation (m + 1)) :
    G.splitMixed pivot y pivot = y (Fin.last m) := by
  simp [splitMixed, G.split_inactive_coordinate hp]

theorem splitMixed_group {n m : ℕ} (G : ProportionalGroups n m) (pivot : Fin n)
    (hp : ∀ g, pivot ∉ G.members g) {i : Fin n} {g : Fin m} (hi : i ∈ G.members g)
    (y : Allocation (m + 1)) : G.splitMixed pivot y i = G.length i / G.total g * y g.castSucc := by
  have hn : i ≠ pivot := by intro he; subst i; exact hp g hi
  simp only [splitMixed, G.split_group_coordinate hi, hn, ite_false, add_zero]

theorem splitMixed_inactive {n m : ℕ} (G : ProportionalGroups n m) (pivot : Fin n)
    {i : Fin n} (hi : ∀ g, i ∉ G.members g) (hne : i ≠ pivot)
    (y : Allocation (m + 1)) : G.splitMixed pivot y i = 0 := by
  simp [splitMixed, G.split_inactive_coordinate hi, hne]

theorem splitMixed_fullBudget {n m : ℕ} (G : ProportionalGroups n m) (pivot : Fin n)
    {B : ℝ} {y : Allocation (m + 1)} (hy : FullBudget B y) :
    FullBudget B (G.splitMixed pivot y) := by
  classical
  constructor
  · intro i
    have hU : 0 ≤ G.split (fun g => y g.castSucc) i :=
      Finset.sum_nonneg (fun g _ => mul_nonneg (G.coefficient_nonnegative g i) (hy.1 g.castSucc))
    apply add_nonneg hU
    split_ifs
    · exact hy.1 _
    · exact le_rfl
  · unfold splitMixed split
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    simp only [← Finset.sum_mul, G.coefficient_sum, one_mul]
    have hp : (∑ i : Fin n, if i = pivot then y (Fin.last m) else 0) = y (Fin.last m) := by simp
    rw [hp, ← Fin.sum_univ_castSucc]
    exact hy.2

theorem measurable_splitMixed {n m : ℕ} (G : ProportionalGroups n m) (pivot : Fin n) :
    Measurable (G.splitMixed pivot) := by
  apply Measurable.of_eval
  intro i
  have hU : Measurable (fun y : Allocation (m + 1) => G.split (fun g => y g.castSucc) i) :=
    Finset.measurable_sum _ (fun g _ => measurable_const.mul (measurable_pi_apply g.castSucc))
  apply hU.add
  by_cases hi : i = pivot
  · simpa only [hi, ite_true] using (measurable_pi_apply (Fin.last m))
  · simpa only [hi, ite_false] using (measurable_const : Measurable (fun _ : Allocation (m + 1) => (0 : ℝ)))

noncomputable def splitMixedLaw {n m : ℕ} (G : ProportionalGroups n m) (pivot : Fin n)
    (μ : Mixed (m + 1)) : Mixed n := μ.map (G.splitMixed pivot)

theorem splitMixedLaw_fullBudget {n m : ℕ} (G : ProportionalGroups n m) (pivot : Fin n)
    {B : ℝ} (μ : Mixed (m + 1)) (hμ : ∀ᵐ y ∂(μ : Measure (Allocation (m + 1))), FullBudget B y) :
    ∀ᵐ x ∂(G.splitMixedLaw pivot μ : Measure (Allocation n)), FullBudget B x := by
  change ∀ᵐ x ∂Measure.map (G.splitMixed pivot) (μ : Measure (Allocation (m + 1))), FullBudget B x
  rw [ae_map_iff (G.measurable_splitMixed pivot).aemeasurable (measurable_fullBudget B)]
  exact hμ.mono fun _ hy => G.splitMixed_fullBudget pivot hy

theorem splitMixedLaw_pivot {n m : ℕ} (G : ProportionalGroups n m) (pivot : Fin n)
    (hp : ∀ g, pivot ∉ G.members g) (μ : Mixed (m + 1)) :
    (marginal (G.splitMixedLaw pivot μ) pivot : Measure ℝ) = (marginal μ (Fin.last m) : Measure ℝ) := by
  change Measure.map (fun x : Allocation n => x pivot)
    (Measure.map (G.splitMixed pivot) (μ : Measure (Allocation (m + 1)))) = _
  rw [Measure.map_map (measurable_pi_apply pivot) (G.measurable_splitMixed pivot)]
  have he : (fun x : Allocation n => x pivot) ∘ G.splitMixed pivot = fun y => y (Fin.last m) :=
    funext (G.splitMixed_pivot pivot hp)
  rw [he]
  rfl

theorem splitMixedLaw_uniform {n m : ℕ} (G : ProportionalGroups n m) (pivot : Fin n)
    (hp : ∀ g, pivot ∉ G.members g) (μ : Mixed (m + 1))
    (hμ : ∀ g, (marginal μ g.castSucc : Measure ℝ) = uniformLaw (G.total g))
    {i : Fin n} {g : Fin m} (hi : i ∈ G.members g) :
    (marginal (G.splitMixedLaw pivot μ) i : Measure ℝ) = uniformLaw (G.length i) := by
  change Measure.map (fun x : Allocation n => x i)
    (Measure.map (G.splitMixed pivot) (μ : Measure (Allocation (m + 1)))) = _
  rw [Measure.map_map (measurable_pi_apply i) (G.measurable_splitMixed pivot)]
  have he : (fun x : Allocation n => x i) ∘ G.splitMixed pivot =
      (fun r : ℝ => G.length i / G.total g * r) ∘ (fun y : Allocation (m + 1) => y g.castSucc) :=
    funext (G.splitMixed_group pivot hp hi)
  rw [he, ← Measure.map_map (g := fun r : ℝ => G.length i / G.total g * r)
    (measurable_const.mul measurable_id) (measurable_pi_apply g.castSucc)]
  change Measure.map (fun r => G.length i / G.total g * r) (marginal μ g.castSucc : Measure ℝ) = _
  rw [hμ g]
  exact scale_uniformLaw (G.length_pos i) (G.total_pos g)

theorem splitMixedLaw_inactive {n m : ℕ} (G : ProportionalGroups n m) (pivot : Fin n)
    (μ : Mixed (m + 1)) {i : Fin n} (hi : ∀ g, i ∉ G.members g) (hne : i ≠ pivot) :
    (marginal (G.splitMixedLaw pivot μ) i : Measure ℝ) = Measure.dirac 0 := by
  change Measure.map (fun x : Allocation n => x i)
    (Measure.map (G.splitMixed pivot) (μ : Measure (Allocation (m + 1)))) = _
  rw [Measure.map_map (measurable_pi_apply i) (G.measurable_splitMixed pivot)]
  have he : (fun x : Allocation n => x i) ∘ G.splitMixed pivot = fun _ : Allocation (m + 1) => (0 : ℝ) :=
    funext (G.splitMixed_inactive pivot hi hne)
  rw [he, Measure.map_const, measure_univ, one_smul]

end ProportionalGroups
end Blotto
