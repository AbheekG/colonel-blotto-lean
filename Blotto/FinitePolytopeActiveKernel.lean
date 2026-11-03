import Blotto.FinitePolytopeVertex

/-! Every midpoint vertex of a finite rational halfspace system has a
trivial common kernel for its active rows. A concrete finite minimum supplies
the radius for both opposite perturbations. Together with the constructed
maximal-margin order-cell vertex this derives active-row injectivity even in
lower affine dimension; no full-rank/vertex witness is an input to that
order-cell endpoint. The separate active-square and rational-witness modules
select the nonsingular subsystem and prove its determinant/Cramer bounds. -/

namespace Blotto.FinitePolytopeActiveKernel
open Set RationalOrderCell FinitePolytopeVertex
open scoped BigOperators Classical

theorem evaluate_perturb {d : Type*} [Fintype d] [DecidableEq d]
    (row : LinearRow d) (x direction : d → ℝ) (step : ℝ) :
    row.evaluate (fun coordinate => x coordinate + step * direction coordinate) =
      row.evaluate x + step * row.evaluate direction := by
  rw [row.evaluate_coefficients,row.evaluate_coefficients,row.evaluate_coefficients]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

theorem residual_perturb {d : Type*} [Fintype d] [DecidableEq d]
    (row : LinearRow d) (x direction : d → ℝ) (step : ℝ) :
    row.residual (fun coordinate => x coordinate + step * direction coordinate) =
      row.residual x + step * row.evaluate direction := by
  unfold LinearRow.residual
  rw [evaluate_perturb]
  ring

noncomputable def allowances {r d : Type*} [Fintype r] (rows : r → LinearRow d)
    (x direction : d → ℝ) : Finset ℝ :=
  insert 1 (Finset.univ.image (fun row => if (rows row).residual x < 0 then
    -(rows row).residual x / (1 + |(rows row).evaluate direction|) else 1))

noncomputable def radius {r d : Type*} [Fintype r] (rows : r → LinearRow d)
    (x direction : d → ℝ) : ℝ := (allowances rows x direction).inf' (Finset.insert_nonempty _ _) id

theorem radius_positive {r d : Type*} [Fintype r] (rows : r → LinearRow d)
    (x direction : d → ℝ) : 0 < radius rows x direction := by
  apply (Finset.lt_inf'_iff _).mpr
  intro value hValue
  rcases Finset.mem_insert.mp hValue with rfl | hValue
  · norm_num
  · obtain ⟨row,_hr,rfl⟩ := Finset.mem_image.mp hValue
    split
    · rename_i hNeg
      exact div_pos (neg_pos.mpr hNeg) (by positivity)
    · norm_num

theorem radius_le_inactive {r d : Type*} [Fintype r] (rows : r → LinearRow d)
    (x direction : d → ℝ) (row : r) (hInactive : (rows row).residual x < 0) :
    radius rows x direction ≤ -(rows row).residual x / (1 + |(rows row).evaluate direction|) := by
  have h : radius rows x direction ≤
      (if (rows row).residual x < 0 then -(rows row).residual x / (1 + |(rows row).evaluate direction|) else 1) := by
    apply Finset.inf'_le
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨row,Finset.mem_univ _,rfl⟩
  simpa only [ite_eq_left hInactive] using h

noncomputable def halfspaces {r d : Type*} (rows : r → LinearRow d) : Set (d → ℝ) :=
  {x | ∀ row, (rows row).residual x ≤ 0}

theorem opposite_perturbations_feasible {r d : Type*} [Fintype r] [Fintype d] [DecidableEq d]
    (rows : r → LinearRow d) (x direction : d → ℝ) (hX : x ∈ halfspaces rows)
    (hKernel : ∀ row, (rows row).residual x = 0 → (rows row).evaluate direction = 0) :
    (fun coordinate => x coordinate + radius rows x direction * direction coordinate) ∈ halfspaces rows ∧
      (fun coordinate => x coordinate - radius rows x direction * direction coordinate) ∈ halfspaces rows := by
  have hRadius := radius_positive rows x direction
  have hEach : ∀ row,
      (rows row).residual (fun coordinate => x coordinate + radius rows x direction * direction coordinate) ≤ 0 ∧
      (rows row).residual (fun coordinate => x coordinate - radius rows x direction * direction coordinate) ≤ 0 := by
    intro row
    have hx := hX row
    by_cases hActive : (rows row).residual x = 0
    · have hEval := hKernel row hActive
      rw [residual_perturb,hActive,hEval]
      constructor
      · simp
      · have hRewrite : (fun coordinate => x coordinate - radius rows x direction * direction coordinate) =
            fun coordinate => x coordinate + (-radius rows x direction) * direction coordinate := by
          funext coordinate; ring
        rw [hRewrite,residual_perturb,hActive,hEval]
        simp
    · have hInactive : (rows row).residual x < 0 := lt_of_le_of_ne hx hActive
      have hAllow := radius_le_inactive rows x direction row hInactive
      have hDen : 0 < 1 + |(rows row).evaluate direction| := by positivity
      have hProduct := (le_div_iff₀ hDen).mp hAllow
      have hUpper := mul_le_mul_of_nonneg_left (le_abs_self ((rows row).evaluate direction)) hRadius.le
      have hLower := mul_le_mul_of_nonneg_left (neg_le_abs ((rows row).evaluate direction)) hRadius.le
      constructor
      · rw [residual_perturb]
        nlinarith
      · have hRewrite : (fun coordinate => x coordinate - radius rows x direction * direction coordinate) =
            fun coordinate => x coordinate + (-radius rows x direction) * direction coordinate := by
          funext coordinate; ring
        rw [hRewrite,residual_perturb]
        nlinarith
  exact ⟨fun row => (hEach row).1,fun row => (hEach row).2⟩

theorem active_kernel_trivial {r d : Type*} [Fintype r] [Fintype d] [DecidableEq d]
    (rows : r → LinearRow d) (vertex : d → ℝ) (hVertex : MidpointVertex (halfspaces rows) vertex)
    (direction : d → ℝ)
    (hKernel : ∀ row, (rows row).residual vertex = 0 → (rows row).evaluate direction = 0) :
    direction = 0 := by
  have hOpposite := opposite_perturbations_feasible rows vertex direction hVertex.1 hKernel
  have hMiddle : FinitePolytopeVertex.midpoint
      (fun coordinate => vertex coordinate + radius rows vertex direction * direction coordinate)
      (fun coordinate => vertex coordinate - radius rows vertex direction * direction coordinate) = vertex := by
    funext coordinate
    unfold FinitePolytopeVertex.midpoint
    ring
  have hFirst := (hVertex.2 _ _ hOpposite.1 hOpposite.2 hMiddle).1
  funext coordinate
  have h := congrFun hFirst coordinate
  have hZero : radius rows vertex direction * direction coordinate = 0 := by linarith
  exact (mul_eq_zero.mp hZero).resolve_left (ne_of_gt (radius_positive rows vertex direction))

/-- The active-kernel property is derived for the actual positive-margin
vertex produced from the old anchors, without an active-system oracle. -/
theorem order_cell_has_injective_active_rows {m K : ℕ} (budgets : Fin 2 → ℚ)
    (original : Variable m K → ℝ) (hOriginal : ∀ v, original v ∈ Icc (0 : ℝ) 1) :
    ∃ vertex : Coordinate m K → ℝ, FeasibleCell budgets original vertex ∧ 0 < vertex none ∧
      (∀ y, FeasibleCell budgets original y → y none ≤ vertex none) ∧
      ∀ direction : Coordinate m K → ℝ,
        (∀ row : CellRow m K, (constraint budgets original row).residual vertex = 0 →
          (constraint budgets original row).evaluate direction = 0) → direction = 0 := by
  obtain ⟨vertex,hVertex,hPositive,hMax⟩ := order_cell_has_positive_vertex budgets original hOriginal
  refine ⟨vertex,hVertex.1,hPositive,hMax,?_⟩
  intro direction hKernel
  exact active_kernel_trivial (constraint budgets original) vertex hVertex direction hKernel

end Blotto.FinitePolytopeActiveKernel
