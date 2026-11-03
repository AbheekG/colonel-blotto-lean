import Blotto.RationalMergeFour
import Blotto.RationalAffineBoxes

/-! Every native four-uniform descriptor endpoint stays inside the four
original lengths, including zero-weight slots used as sampler fallback. -/

namespace Blotto

namespace RationalMergeFourInput

theorem segmentLottery_box (i : RationalMergeFourInput) (slot : Fin 9) :
    InBox ![(i.l0 : ℝ), (i.l1 : ℝ), (i.l2 : ℝ), (i.l3 : ℝ)] (i.segmentLottery.real.P slot) ∧
      InBox ![(i.l0 : ℝ), (i.l1 : ℝ), (i.l2 : ℝ), (i.l3 : ℝ)] (i.segmentLottery.real.Q slot) := by
  unfold segmentLottery
  rw [RationalSegmentLottery.mapped_real, RationalThreeSpec.segmentLottery_real]
  constructor
  · apply RationalAffineAllocation.splitFirstTwo_box i.l0 i.l1 i.l0_pos i.l1_pos
    have h := i.childSpec.real.segmentLottery_box.1 slot
    change InBox ![((i.l0 + i.l1 : ℚ) : ℝ), (i.l2 : ℝ), (i.l3 : ℝ)] _ at h
    exact h
  · apply RationalAffineAllocation.splitFirstTwo_box i.l0 i.l1 i.l0_pos i.l1_pos
    have h := i.childSpec.real.segmentLottery_box.2 slot
    change InBox ![((i.l0 + i.l1 : ℚ) : ℝ), (i.l2 : ℝ), (i.l3 : ℝ)] _ at h
    exact h

end RationalMergeFourInput

namespace RationalFourInput

theorem smallUniformLottery_endpoints (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (slot : Fin 9) :
    FullBudget (i.B : ℝ) ((i.smallUniformLottery hcase).real.P slot) ∧
      FullBudget (i.B : ℝ) ((i.smallUniformLottery hcase).real.Q slot) :=
  (i.smallUniformInput hcase).segmentLottery_endpoints slot

theorem smallUniformLottery_box (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (slot : Fin 9) :
    InBox ![(i.u : ℝ), (i.v : ℝ), (i.w : ℝ), (i.ell : ℝ)] ((i.smallUniformLottery hcase).real.P slot) ∧
      InBox ![(i.u : ℝ), (i.v : ℝ), (i.w : ℝ), (i.ell : ℝ)] ((i.smallUniformLottery hcase).real.Q slot) := by
  rw [smallUniformLottery, i.smallUniformInput_refines]
  have h := (i.smallUniformInputReference hcase).segmentLottery_box slot
  have hl : ∀ L : ℚ, 0 ≤ L → (i.scaleFraction * L : ℚ) ≤ L := by
    intro L hL
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_of_lt i.scaleFraction_bounds.2) hL
  have hlen : ∀ j : Fin 4,
      ![((i.scaleFraction * i.u : ℚ) : ℝ), ((i.scaleFraction * i.v : ℚ) : ℝ), ((i.scaleFraction * i.w : ℚ) : ℝ), (i.ell : ℝ)] j ≤
        ![(i.u : ℝ), (i.v : ℝ), (i.w : ℝ), (i.ell : ℝ)] j := by
    intro j
    fin_cases j
    · change ((i.scaleFraction * i.u : ℚ) : ℝ) ≤ (i.u : ℝ)
      exact_mod_cast hl i.u (le_of_lt i.u_pos)
    · change ((i.scaleFraction * i.v : ℚ) : ℝ) ≤ (i.v : ℝ)
      exact_mod_cast hl i.v (le_of_lt i.lengths_positive.1)
    · change ((i.scaleFraction * i.w : ℚ) : ℝ) ≤ (i.w : ℝ)
      exact_mod_cast hl i.w (le_of_lt i.lengths_positive.2.1)
    · exact le_rfl
  exact ⟨inBox_mono hlen h.1, inBox_mono hlen h.2⟩

end RationalFourInput
end Blotto
