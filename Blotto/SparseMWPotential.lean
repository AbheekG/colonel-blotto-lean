import Blotto.ProductSamplerLawContract

/-! First exact sparse-MW ingredients retained by R136/R143 and R162/R165:
value-weighted single-field losses are bounded/unbiased, and changing one
rounded rational field changes the whole product by only its multiplier.
The effective-loss theorem uses explicit certificates for the exponential
approximation and downward significand rounding. Their actual implementations,
entropy regret and stochastic convergence remain separate obligations. -/

/- Source chain: `notes/proofs/R136.md` §§1–2, `notes/proofs/R143.md` §2,
`notes/proofs/R162.md` §§1,7 and `notes/proofs/R165.md` §2. The concrete
floor/scale primitive is the arithmetic formula in result R124 and retained
`notes/code/general/dependencies/legacy/dyadic_weights.py::round_down`.
The scale must be selected and its significand-width property proved separately. -/

namespace Blotto
open scoped BigOperators Classical

namespace SparseMW

def selectedLoss {m : ℕ} (loss : Fin m → ℝ) (selected : Fin m) : ℝ := loss selected

theorem selectedLoss_unit {m : ℕ} (loss : Fin m → ℝ) (h : ∀ j, 0 ≤ loss j ∧ loss j ≤ 1)
    (selected : Fin m) : 0 ≤ selectedLoss loss selected ∧ selectedLoss loss selected ≤ 1 := h selected

theorem selectedLoss_mean {m : ℕ} (values : Values m) (loss : Fin m → ℝ) :
    (∑ selected, values.weight selected * selectedLoss loss selected) =
      ∑ j, values.weight j * loss j := rfl

theorem weightedLoss_unit {m : ℕ} (values : Values m) (loss : Fin m → ℝ)
    (h : ∀ j, 0 ≤ loss j ∧ loss j ≤ 1) :
    0 ≤ (∑ j, values.weight j * loss j) ∧ (∑ j, values.weight j * loss j) ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (values.positive j).le (h j).1)
  · calc
      _ ≤ ∑ j, values.weight j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_of_le_one_right (values.positive j).le (h j).2
      _ = 1 := values.normalized

theorem selectedLoss_noise_bound {m : ℕ} (values : Values m) (loss : Fin m → ℝ)
    (h : ∀ j, 0 ≤ loss j ∧ loss j ≤ 1) (selected : Fin m) :
    |selectedLoss loss selected - ∑ j, values.weight j * loss j| ≤ 1 := by
  have hs := selectedLoss_unit loss h selected
  have hm := weightedLoss_unit values loss h
  rw [abs_le]
  constructor <;> linarith

theorem selectedLoss_noise_mean_zero {m : ℕ} (values : Values m) (loss : Fin m → ℝ) :
    (∑ selected, values.weight selected *
      (selectedLoss loss selected - ∑ j, values.weight j * loss j)) = 0 := by
  simp only [selectedLoss, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, values.normalized, one_mul, sub_self]

def update {m : ℕ} (weights : Fin m → ℚ) (selected : Fin m) (multiplier : ℚ) : Fin m → ℚ :=
  Function.update weights selected (weights selected * multiplier)

theorem update_selected {m : ℕ} (weights : Fin m → ℚ) (selected : Fin m) (multiplier : ℚ) :
    update weights selected multiplier selected = weights selected * multiplier := by
  simp [update]

theorem update_other {m : ℕ} (weights : Fin m → ℚ) (selected other : Fin m) (multiplier : ℚ)
    (h : other ≠ selected) : update weights selected multiplier other = weights other := by
  simp [update, h]

theorem update_product {m : ℕ} (weights : Fin m → ℚ) (selected : Fin m) (multiplier : ℚ) :
    (∏ j, update weights selected multiplier j) = (∏ j, weights j) * multiplier := by
  unfold update
  rw [Finset.prod_update_of_mem (Finset.mem_univ selected)]
  have he := Finset.prod_erase_mul (Finset.univ : Finset (Fin m)) weights (Finset.mem_univ selected)
  rw [← he]
  simp only [Finset.sdiff_singleton_eq_erase]
  ring

theorem update_positive {m : ℕ} (weights : Fin m → ℚ) (selected : Fin m) (multiplier : ℚ)
    (hw : ∀ j, 0 < weights j) (hm : 0 < multiplier) : ∀ j, 0 < update weights selected multiplier j := by
  intro j
  by_cases he : j = selected
  · subst j
    rw [update_selected]
    exact mul_pos (hw _) hm
  · rw [update_other weights selected j multiplier he]
    exact hw j

theorem update_decreases {m : ℕ} (weights : Fin m → ℚ) (selected : Fin m) (multiplier : ℚ)
    (hw : ∀ j, 0 ≤ weights j) (hm : multiplier ≤ 1) : ∀ j, update weights selected multiplier j ≤ weights j := by
  intro j
  by_cases he : j = selected
  · subst j
    rw [update_selected]
    exact mul_le_of_le_one_right (hw _) hm
  · rw [update_other weights selected j multiplier he]

theorem update_product_ratio {m : ℕ} (weights : Fin m → ℚ) (selected : Fin m) (multiplier : ℚ)
    (hw : ∀ j, 0 < weights j) :
    (∏ j, update weights selected multiplier j) / (∏ j, weights j) = multiplier := by
  rw [update_product]
  have hp : 0 < ∏ j, weights j := Finset.prod_pos (fun j _ => hw j)
  field_simp

def gridRound (x unit : ℚ) : ℚ := (Int.floor (x / unit) : ℚ) * unit

theorem gridRound_down (x unit : ℚ) (hu : 0 < unit) : gridRound x unit ≤ x := by
  have he := mul_le_mul_of_nonneg_right (Int.floor_le (x / unit)) hu.le
  rw [div_mul_cancel₀ _ (ne_of_gt hu)] at he
  exact he

theorem gridRound_error (x unit : ℚ) (hu : 0 < unit) : x < gridRound x unit + unit := by
  have he := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x / unit)) hu
  rw [div_mul_cancel₀ _ (ne_of_gt hu)] at he
  simpa only [gridRound, add_mul, one_mul] using he

theorem gridRound_positive (x unit : ℚ) (hu : 0 < unit) (hx : unit ≤ x) : 0 < gridRound x unit := by
  have hr : (1 : ℚ) ≤ x / unit := (le_div_iff₀ hu).mpr (by simpa only [one_mul] using hx)
  have hf : (0 : ℤ) < Int.floor (x / unit) := Int.floor_pos.mpr hr
  have hfq : (0 : ℚ) < (Int.floor (x / unit) : ℚ) := by exact_mod_cast hf
  exact mul_pos hfq hu

theorem gridRound_relative (x unit theta : ℚ) (hu : 0 < unit)
    (hprecision : unit ≤ theta * gridRound x unit) :
    gridRound x unit ≤ x ∧ x < (1 + theta) * gridRound x unit := by
  refine ⟨gridRound_down x unit hu, ?_⟩
  have he := gridRound_error x unit hu
  nlinarith

theorem gridRound_ratio (x unit theta : ℚ) (hu : 0 < unit) (hx : unit ≤ x)
    (ht : 0 ≤ theta) (hprecision : unit ≤ theta * gridRound x unit) :
    0 < gridRound x unit / x ∧ gridRound x unit / x ≤ 1 ∧
      1 / (1 + theta) < gridRound x unit / x := by
  have hp := gridRound_positive x unit hu hx
  have hx0 : 0 < x := hu.trans_le hx
  have he := gridRound_relative x unit theta hu hprecision
  refine ⟨div_pos hp hx0, (div_le_one hx0).mpr he.1, ?_⟩
  have ht1 : 0 < 1 + theta := by linarith
  apply (div_lt_div_iff₀ ht1 hx0).mpr
  nlinarith

def significandRoundAtScale (x scale : ℚ) (bits : ℕ) : ℚ :=
  gridRound x (scale / (2 : ℚ) ^ bits)

theorem significandRoundAtScale_certificate (x scale : ℚ) (bits : ℕ)
    (hscale : 0 < scale) (hx : scale ≤ x) :
    0 < significandRoundAtScale x scale bits ∧
      significandRoundAtScale x scale bits ≤ x ∧
      x < (1 + 1 / (2 : ℚ) ^ bits) * significandRoundAtScale x scale bits := by
  let count : ℚ := (2 : ℚ) ^ bits
  have hc : 0 < count := by dsimp [count]; positivity
  have hc1 : 1 ≤ count := one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2)
  let unit := scale / count
  have hu : 0 < unit := div_pos hscale hc
  have hus : unit ≤ scale := (div_le_self hscale.le hc1)
  have hux : unit ≤ x := hus.trans hx
  have hRatio : count ≤ x / unit := by
    apply (le_div_iff₀ hu).mpr
    have he : count * unit = scale := by dsimp [unit]; field_simp
    rw [he]
    exact hx
  have hcountInt : ∃ n : ℤ, (n : ℚ) = count := ⟨(2 : ℤ) ^ bits, by dsimp [count]; norm_cast⟩
  rcases hcountInt with ⟨n, hn⟩
  have hfloor : count ≤ (Int.floor (x / unit) : ℚ) := by
    rw [← hn]
    exact_mod_cast (Int.le_floor.mpr (by simpa only [hn] using hRatio) : n ≤ Int.floor (x / unit))
  have hrounded : scale ≤ gridRound x unit := by
    have he := mul_le_mul_of_nonneg_right hfloor hu.le
    have hs : count * unit = scale := by dsimp [unit]; field_simp
    rw [hs] at he
    exact he
  have hprecision : unit ≤ (1 / count) * gridRound x unit := by
    change scale / count ≤ (1 / count) * gridRound x unit
    have he := div_le_div_of_nonneg_right hrounded hc.le
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using he
  have he := gridRound_relative x unit (1 / count) hu hprecision
  exact ⟨gridRound_positive x unit hu hux, he.1, he.2⟩

noncomputable def effectiveLoss (eta multiplier : ℝ) : ℝ := -Real.log multiplier / eta

theorem effectiveLoss_exact {eta multiplier : ℝ} (heta : eta ≠ 0) (hm : 0 < multiplier) :
    Real.exp (-eta * effectiveLoss eta multiplier) = multiplier := by
  have he : -eta * effectiveLoss eta multiplier = Real.log multiplier := by
    unfold effectiveLoss
    field_simp
  rw [he, Real.exp_log hm]

theorem effectiveLoss_error {eta loss error multiplier : ℝ} (heta : 0 < eta)
    (hlo : Real.exp (-eta * loss - error) ≤ multiplier)
    (hhi : multiplier ≤ Real.exp (-eta * loss)) :
    loss ≤ effectiveLoss eta multiplier ∧ effectiveLoss eta multiplier ≤ loss + error / eta := by
  have hm : 0 < multiplier := (Real.exp_pos _).trans_le hlo
  have hl := Real.log_le_log (Real.exp_pos _) hlo
  have hh := Real.log_le_log hm hhi
  rw [Real.log_exp] at hl hh
  unfold effectiveLoss
  constructor
  · apply (le_div_iff₀ heta).mpr
    linarith
  · apply (div_le_iff₀ heta).mpr
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt heta)]
    linarith

theorem two_rounded_multiplier_certificate {eta loss theta approximation multiplier : ℝ}
    (hApproxLower : Real.exp (-eta * loss - 2 * theta) ≤ approximation)
    (hApproxUpper : approximation ≤ Real.exp (-eta * loss))
    (hRoundLower : Real.exp (-2 * theta) * approximation ≤ multiplier)
    (hRoundUpper : multiplier ≤ approximation) :
    Real.exp (-eta * loss - 4 * theta) ≤ multiplier ∧ multiplier ≤ Real.exp (-eta * loss) := by
  constructor
  · calc
      Real.exp (-eta * loss - 4 * theta) =
          Real.exp (-2 * theta) * Real.exp (-eta * loss - 2 * theta) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-2 * theta) * approximation :=
        mul_le_mul_of_nonneg_left hApproxLower (Real.exp_pos _).le
      _ ≤ multiplier := hRoundLower
  · exact hRoundUpper.trans hApproxUpper

theorem rounded_sparse_loss_error {eta loss theta approximation multiplier : ℝ} (heta : 0 < eta)
    (hApproxLower : Real.exp (-eta * loss - 2 * theta) ≤ approximation)
    (hApproxUpper : approximation ≤ Real.exp (-eta * loss))
    (hRoundLower : Real.exp (-2 * theta) * approximation ≤ multiplier)
    (hRoundUpper : multiplier ≤ approximation) :
    loss ≤ effectiveLoss eta multiplier ∧ effectiveLoss eta multiplier ≤ loss + 4 * theta / eta := by
  have he := two_rounded_multiplier_certificate hApproxLower hApproxUpper hRoundLower hRoundUpper
  exact effectiveLoss_error heta he.1 he.2

end SparseMW
end Blotto
