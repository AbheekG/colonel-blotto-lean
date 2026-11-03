import Blotto.FourReflectedResources
import Blotto.FourSmallUniforms

/-! Exact marginal recovery when the uniform and reflected-atom branches are
combined. Both branch laws were constructed independently beforehand. -/

namespace Blotto.FourInput
open MeasureTheory Set

theorem reflected_weight_identity (i : FourInput) :
    (1 - i.p) * i.nestedProbability = i.shortFraction * (i.p / i.scaleFraction) := by
  have hS := ne_of_gt i.lengths_positive.2.2.2
  have hc := ne_of_gt i.scaleFraction_bounds.1
  have hq : i.nestedProbability = i.p * i.ell / (i.scaleFraction * i.S) := by
    apply (eq_div_iff (mul_ne_zero hc hS)).mpr
    simpa only [mul_assoc] using i.scaled_resource_identity.2
  rw [hq]
  dsimp [shortFraction]
  field_simp [hc, hS]

theorem reflected_base_identity (i : FourInput) :
    (1 - i.p) * (1 - i.nestedProbability) + i.p / i.scaleFraction = 1 := by
  have hc := ne_of_gt i.scaleFraction_bounds.1
  have he : i.scaleFraction * (i.p / i.scaleFraction) = i.p := by field_simp [hc]
  calc
    _ = 1 - i.p - (1 - i.p) * i.nestedProbability + i.p / i.scaleFraction := by ring
    _ = 1 - i.p - i.shortFraction * (i.p / i.scaleFraction) + i.p / i.scaleFraction := by
      rw [i.reflected_weight_identity]
    _ = 1 - i.p + i.scaleFraction * (i.p / i.scaleFraction) := by dsimp [scaleFraction]; ring
    _ = 1 := by rw [he]; ring

/-- An exact measure identity on the entire original interval, including all
endpoint events. No density subtraction is used as a definition of a law. -/
theorem reflection_recovery (i : FourInput) {L : ℝ} (hL : 0 < L) :
    ENNReal.ofReal i.p • uniformLaw (i.scaleFraction * L) +
      ENNReal.ofReal (1 - i.p) •
        (ENNReal.ofReal i.nestedProbability • (affineUniform (i.scaleFraction * L) L : Measure ℝ) +
          ENNReal.ofReal (1 - i.nestedProbability) • uniformLaw L) = uniformLaw L := by
  have hc := i.scaleFraction_bounds
  have hq := i.nestedProbability_bounds
  have hp := le_of_lt i.p_pos
  have hp' := sub_nonneg.mpr (le_of_lt i.p_lt)
  have hCL : 0 < i.scaleFraction * L := mul_pos hc.1 hL
  have hCLL : i.scaleFraction * L ≤ L := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_of_lt hc.2) (le_of_lt hL)
  let r : ℝ := i.p / (i.scaleFraction * L)
  let s : ℝ := (1 - i.p) * (1 - i.nestedProbability)
  have hr : 0 ≤ r := div_nonneg hp (le_of_lt hCL)
  have hs : 0 ≤ s := mul_nonneg hp' (sub_nonneg.mpr (le_of_lt hq.2))
  have hmass : (1 - i.p) * i.nestedProbability = (L - i.scaleFraction * L) * r := by
    rw [i.reflected_weight_identity]
    have he : L - i.scaleFraction * L = i.shortFraction * L := by dsimp [scaleFraction]; ring
    rw [he]
    dsimp [r]
    field_simp [ne_of_gt hL, ne_of_gt hc.1]
  have hfull : ENNReal.ofReal (i.p / i.scaleFraction) • uniformLaw L =
      ENNReal.ofReal r • rawInterval 0 L := by
    rw [← affineUniform_zero_uniformLaw hL]
    have he : i.p / i.scaleFraction = (L - 0) * r := by
      dsimp [r]
      simp only [sub_zero]
      field_simp [ne_of_gt hL, ne_of_gt hc.1]
    rw [he, weighted_affine_interval (le_of_lt hL) hr]
  rw [← affineUniform_zero_uniformLaw hCL, affineUniform_scaled_interval hCL hp,
    smul_add, smul_smul, smul_smul, ← ENNReal.ofReal_mul hp', ← ENNReal.ofReal_mul hp',
    hmass, weighted_affine_interval hCLL hr]
  simp only [sub_zero]
  change ENNReal.ofReal r • rawInterval 0 (i.scaleFraction * L) +
    (ENNReal.ofReal r • rawInterval (i.scaleFraction * L) L + ENNReal.ofReal s • uniformLaw L) = _
  rw [← add_assoc, rawInterval_scaled_glue (le_of_lt hCL) hCLL, ← hfull,
    ← add_smul, ← ENNReal.ofReal_add (div_nonneg hp (le_of_lt hc.1)) hs]
  have he : i.p / i.scaleFraction + s = 1 := by dsimp [s]; linarith [i.reflected_base_identity]
  rw [he, ENNReal.ofReal_one, one_smul]

noncomputable def smallCaseLaw (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) : Mixed 4 :=
  binaryLaw i.p ⟨le_of_lt i.p_pos, le_of_lt i.p_lt⟩ (i.smallUniformLaw hcase) (i.reflectedZeroLaw hcase)

theorem smallCaseLaw_contract (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    (∀ᵐ x ∂(i.smallCaseLaw hcase : Measure (Allocation 4)), FullBudget i.B x) ∧
      (marginal (i.smallCaseLaw hcase) 0 : Measure ℝ) = uniformLaw i.u ∧
      (marginal (i.smallCaseLaw hcase) 1 : Measure ℝ) = uniformLaw i.v ∧
      (marginal (i.smallCaseLaw hcase) 2 : Measure ℝ) = uniformLaw i.w ∧
      (marginal (i.smallCaseLaw hcase) 3 : Measure ℝ) = zeroUniformLaw i.ell i.p := by
  have hU := i.smallUniformLaw_contract hcase
  have hR := i.reflectedZeroLaw_fullBudget hcase
  have hj : ∀ j : Fin 3, (marginal (i.smallCaseLaw hcase) j.castSucc : Measure ℝ) = uniformLaw (i.originalLengths j) := by
    intro j
    rw [smallCaseLaw, binaryLaw_marginal, i.reflectedZeroLaw_marginal hcase j]
    have hm : (marginal (i.smallUniformLaw hcase) j.castSucc : Measure ℝ) = uniformLaw (i.scaleFraction * i.originalLengths j) := by
      fin_cases j
      · exact hU.2.1
      · exact hU.2.2.1
      · exact hU.2.2.2.1
    rw [hm]
    exact i.reflection_recovery (i.originalLengths_pos j)
  refine ⟨binaryLaw_fullBudget _ _ _ _ hU.1 hR, ?_, ?_, ?_, ?_⟩
  · exact hj 0
  · exact hj 1
  · exact hj 2
  · rw [smallCaseLaw, binaryLaw_marginal, hU.2.2.2.2, i.reflectedZeroLaw_last hcase]
    unfold zeroUniformLaw
    rw [add_comm]

noncomputable def smallCasePoint (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) (useUniform : Bool)
    (choice : ℕ → Bool) (useFamily : Bool) (r t : ℝ) (edge : Fin 9) (residualEdge : Fin 3) : Allocation 4 :=
  if useUniform then (i.smallUniformInput hcase).point edge t else
    i.reflectedZeroPoint hcase choice useFamily r t edge residualEdge

theorem smallCasePoint_fullBudget (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) (useUniform : Bool)
    (choice : ℕ → Bool) (useFamily : Bool) {r t : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (edge : Fin 9) (residualEdge : Fin 3) : FullBudget i.B (i.smallCasePoint hcase useUniform choice useFamily r t edge residualEdge) := by
  unfold smallCasePoint
  split_ifs
  · exact i.smallUniformPoint_fullBudget hcase edge ht
  · exact i.reflectedZeroPoint_fullBudget hcase choice useFamily hr ht edge residualEdge

end Blotto.FourInput
