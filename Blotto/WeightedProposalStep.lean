import Blotto.WeightedGuideTree

/-! Local fork facts for the augmented R160 proposal. Every recursive-law,
resource and importance hypothesis is explicit; this file does not claim that
the full recursive sampler or its rejection loop has been implemented. -/

namespace Blotto
open scoped BigOperators Classical

namespace WeightedResourceFamily

theorem selected_prefix_positive {n : ℕ} (a : WeightedResourceFamily n)
    (i : Fin n) (t : ℝ) (hr : a.resource i ≤ t) (hm : 0 < a.mass i) :
    0 < a.prefixMass t := by
  have hn : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ if a.resource j ≤ t then a.mass j else 0 := by
    intro j _
    split_ifs
    · exact a.mass_nonnegative j
    · exact le_rfl
  have he := Finset.single_le_sum hn (Finset.mem_univ i)
  exact hm.trans_le (by simpa only [prefixMass, hr, ite_true] using he)

theorem selected_convolution_positive {n m : ℕ} (a : WeightedResourceFamily n)
    (b : WeightedResourceFamily m) (i : Fin n) (B : ℝ)
    (hs : 0 < a.mass i * b.prefixMass (B - a.resource i)) :
    0 < a.convolution b B := by
  rw [convolution_prefix_right]
  have hn : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ a.mass j * b.prefixMass (B - a.resource j) :=
    fun j _ => mul_nonneg (a.mass_nonnegative j) (b.prefix_nonnegative _)
  exact hs.trans_le (Finset.single_le_sum hn (Finset.mem_univ i))

noncomputable def syntheticChoice {n m : ℕ} (a : WeightedResourceFamily n)
    (b : WeightedResourceFamily m) (B : ℝ) (i : Fin n) : ℝ :=
  a.mass i * b.prefixMass (B - a.resource i) / a.convolution b B

theorem syntheticChoice_nonnegative {n m : ℕ} (a : WeightedResourceFamily n)
    (b : WeightedResourceFamily m) (B : ℝ) (i : Fin n) :
    0 ≤ a.syntheticChoice b B i :=
  div_nonneg (mul_nonneg (a.mass_nonnegative i) (b.prefix_nonnegative _))
    (a.convolution_nonnegative b B)

theorem syntheticChoice_sum {n m : ℕ} (a : WeightedResourceFamily n)
    (b : WeightedResourceFamily m) (B : ℝ) (h : 0 < a.convolution b B) :
    ∑ i, a.syntheticChoice b B i = 1 := by
  unfold syntheticChoice
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← convolution_prefix_right, mul_inv_cancel₀ (ne_of_gt h)]

noncomputable def auxiliaryChoice {n : ℕ} (a : WeightedResourceFamily n)
    (t : ℝ) (i : Fin n) : ℝ :=
  if a.resource i ≤ t then a.mass i / a.prefixMass t else 0

theorem auxiliaryChoice_nonnegative {n : ℕ} (a : WeightedResourceFamily n)
    (t : ℝ) (i : Fin n) : 0 ≤ a.auxiliaryChoice t i := by
  unfold auxiliaryChoice
  split_ifs
  · exact div_nonneg (a.mass_nonnegative i) (a.prefix_nonnegative t)
  · exact le_rfl

theorem auxiliaryChoice_sum {n : ℕ} (a : WeightedResourceFamily n)
    (t : ℝ) (h : 0 < a.prefixMass t) : ∑ i, a.auxiliaryChoice t i = 1 := by
  have he : (∑ i, a.auxiliaryChoice t i) = a.prefixMass t / a.prefixMass t := by
    unfold auxiliaryChoice prefixMass
    simp only [div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [he, div_self (ne_of_gt h)]

theorem auxiliaryChoice_feasible_right {n : ℕ} (a : WeightedResourceFamily n)
    (B cRight : ℝ) (i : Fin n) (h : 0 < a.auxiliaryChoice (B - cRight) i) :
    cRight ≤ B - a.resource i := by
  by_cases hr : a.resource i ≤ B - cRight
  · linarith
  · simp only [auxiliaryChoice, hr, ite_false, lt_self_iff_false] at h

end WeightedResourceFamily

namespace WeightedProposalStep

noncomputable def importance (Z RLeft RRight HLeft HRight : ℝ) : ℝ :=
  Z * RLeft * RRight / (HLeft * HRight)

noncomputable def pathProbability (atom HRight Z qLeft qRight : ℝ) : ℝ :=
  (atom * HRight / Z) * qRight * qLeft

noncomputable def auxiliaryPath (atom HLeft aLeft aRight : ℝ) : ℝ :=
  (atom / HLeft) * aRight * aLeft

theorem selected_denominators_positive {n m : ℕ} (left : WeightedResourceFamily n)
    (right : WeightedResourceFamily m) (i : Fin n) (B cRight : ℝ)
    (hselected : 0 < left.mass i * right.prefixMass (B - left.resource i))
    (hr : cRight ≤ B - left.resource i) :
    0 < right.prefixMass (B - left.resource i) ∧ 0 < left.prefixMass (B - cRight) := by
  have hm : 0 < left.mass i := by
    by_contra hn
    have hz : left.mass i = 0 :=
      le_antisymm (le_of_not_gt hn) (left.mass_nonnegative i)
    simp only [hz, zero_mul, lt_self_iff_false] at hselected
  have hright : 0 < right.prefixMass (B - left.resource i) := by
    by_contra hn
    have hz : right.prefixMass (B - left.resource i) = 0 :=
      le_antisymm (le_of_not_gt hn) (right.prefix_nonnegative _)
    simp only [hz, mul_zero, lt_self_iff_false] at hselected
  exact ⟨hright, left.selected_prefix_positive i _ (by linarith) hm⟩

theorem pair_feasible (B cLeft cRight : ℝ) (hl : 0 ≤ cLeft) (hr : 0 ≤ cRight)
    (hleft : cLeft ≤ B - cRight) : 0 ≤ cLeft + cRight ∧ cLeft + cRight ≤ B := by
  exact ⟨add_nonneg hl hr, by linarith⟩

theorem pair_feasible_at_closed_budget (B cLeft cRight : ℝ)
    (hleft : cLeft ≤ B - cRight) : cLeft + cRight ≤ B := by
  linarith

theorem importance_positive {Z RLeft RRight HLeft HRight : ℝ}
    (hZ : 0 < Z) (hL : 0 < RLeft) (hR : 0 < RRight)
    (hHL : 0 < HLeft) (hHR : 0 < HRight) :
    0 < importance Z RLeft RRight HLeft HRight :=
  div_pos (mul_pos (mul_pos hZ hL) hR) (mul_pos hHL hHR)

theorem importance_bound {Z RLeft RRight HLeft HRight GLeft GRight : ℝ}
    (hZ : 0 ≤ Z) (hR : 0 ≤ RRight)
    (hHL : 0 < HLeft) (hHR : 0 < HRight) (hGL : 0 ≤ GLeft)
    (hLeft : RLeft / HLeft ≤ GLeft) (hRight : RRight / HRight ≤ GRight) :
    importance Z RLeft RRight HLeft HRight ≤ Z * GLeft * GRight := by
  have he : importance Z RLeft RRight HLeft HRight =
      Z * (RLeft / HLeft) * (RRight / HRight) := by
    unfold importance
    field_simp
  rw [he]
  have hr0 : 0 ≤ RRight / HRight := div_nonneg hR hHR.le
  exact mul_le_mul (mul_le_mul_of_nonneg_left hLeft hZ) hRight hr0 (mul_nonneg hZ hGL)

theorem selected_fork_contract {n m : ℕ} (left : WeightedResourceFamily n)
    (right : WeightedResourceFamily m) (i : Fin n) (B cLeft cRight RLeft RRight GLeft GRight : ℝ)
    (hselected : 0 < left.mass i * right.prefixMass (B - left.resource i))
    (hRightResource : cRight ≤ B - left.resource i)
    (hLeftResource : cLeft ≤ B - cRight)
    (hRLeft : 0 < RLeft) (hRRight : 0 < RRight) (hGLeft : 0 ≤ GLeft)
    (hLeftRatio : RLeft / left.prefixMass (B - cRight) ≤ GLeft)
    (hRightRatio : RRight / right.prefixMass (B - left.resource i) ≤ GRight) :
    let Z := left.convolution right B
    let R := importance Z RLeft RRight
      (left.prefixMass (B - cRight)) (right.prefixMass (B - left.resource i))
    0 < Z ∧ 0 < right.prefixMass (B - left.resource i) ∧
      0 < left.prefixMass (B - cRight) ∧ cLeft + cRight ≤ B ∧
      0 < R ∧ R ≤ Z * GLeft * GRight := by
  dsimp only
  have hZ := left.selected_convolution_positive right i B hselected
  have hd := selected_denominators_positive left right i B cRight hselected hRightResource
  refine ⟨hZ, hd.1, hd.2, pair_feasible_at_closed_budget B cLeft cRight hLeftResource, ?_, ?_⟩
  · exact importance_positive hZ hRLeft hRRight hd.2 hd.1
  · exact importance_bound hZ.le hRRight.le hd.2 hd.1 hGLeft hLeftRatio hRightRatio

theorem path_cancellation {atom Z HLeft HRight qLeft qRight RLeft RRight
    wLeft wRight aLeft aRight : ℝ}
    (hZ : Z ≠ 0) (hHL : HLeft ≠ 0) (hHR : HRight ≠ 0)
    (hLeft : qLeft * RLeft = wLeft * aLeft)
    (hRight : qRight * RRight = wRight * aRight) :
    pathProbability atom HRight Z qLeft qRight * importance Z RLeft RRight HLeft HRight =
      (wLeft * wRight) * auxiliaryPath atom HLeft aLeft aRight := by
  have he : pathProbability atom HRight Z qLeft qRight * importance Z RLeft RRight HLeft HRight =
      atom / HLeft * (qLeft * RLeft) * (qRight * RRight) := by
    unfold pathProbability importance
    field_simp [hZ, hHL, hHR]
  rw [he, hLeft, hRight]
  unfold auxiliaryPath
  ring

theorem selected_path_cancellation {n m : ℕ} (left : WeightedResourceFamily n)
    (right : WeightedResourceFamily m) (i : Fin n)
    (B cRight qLeft qRight RLeft RRight wLeft wRight aLeft aRight : ℝ)
    (hselected : 0 < left.mass i * right.prefixMass (B - left.resource i))
    (hresource : cRight ≤ B - left.resource i)
    (hLeft : qLeft * RLeft = wLeft * aLeft)
    (hRight : qRight * RRight = wRight * aRight) :
    pathProbability (left.mass i) (right.prefixMass (B - left.resource i))
        (left.convolution right B) qLeft qRight *
      importance (left.convolution right B) RLeft RRight
        (left.prefixMass (B - cRight)) (right.prefixMass (B - left.resource i)) =
      (wLeft * wRight) * auxiliaryPath (left.mass i)
        (left.prefixMass (B - cRight)) aLeft aRight := by
  have hZ := left.selected_convolution_positive right i B hselected
  have hd := selected_denominators_positive left right i B cRight hselected hresource
  exact path_cancellation (ne_of_gt hZ) (ne_of_gt hd.2) (ne_of_gt hd.1) hLeft hRight

theorem parent_guide_ratio_bound {R Z H GLeft GRight gamma : ℝ}
    (hH : 0 < H) (hGLeft : 0 ≤ GLeft) (hGRight : 0 ≤ GRight)
    (hR : R ≤ Z * GLeft * GRight) (hlocal : Z ≤ gamma * H) :
    R / H ≤ gamma * GLeft * GRight := by
  apply (div_le_iff₀ hH).mpr
  calc
    R ≤ Z * GLeft * GRight := hR
    _ ≤ (gamma * H) * GLeft * GRight :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hlocal hGLeft) hGRight
    _ = (gamma * GLeft * GRight) * H := by ring

theorem upper_guide_ratio_bound {R Z H : ℝ} (hH : 0 < H)
    (hR : R ≤ Z) (hlocal : Z ≤ H) : R / H ≤ 1 := by
  apply (div_le_iff₀ hH).mpr
  simpa only [one_mul] using hR.trans hlocal

theorem auxiliaryPath_sum {n k l : ℕ} (guide : WeightedResourceFamily n)
    (cutoff : ℝ) (hguide : 0 < guide.prefixMass cutoff)
    (aLeft : Fin n → Fin k → ℝ) (aRight : Fin n → Fin l → ℝ)
    (hLeft : ∀ i, ∑ j, aLeft i j = 1) (hRight : ∀ i, ∑ j, aRight i j = 1) :
    (∑ i, ∑ r, ∑ s, guide.auxiliaryChoice cutoff i * aRight i r * aLeft i s) = 1 := by
  simp_rw [← Finset.mul_sum, hLeft, mul_one, ← Finset.mul_sum, hRight, mul_one]
  exact guide.auxiliaryChoice_sum cutoff hguide

end WeightedProposalStep
end Blotto
