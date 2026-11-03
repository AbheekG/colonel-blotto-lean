import Blotto.RationalAffineAllocation
import Blotto.RationalFourInput
import Blotto.RationalFourParameterTable

/-! Native merging/splitting for the four-uniform branch. The computed
descriptor is the exact push-forward of the verified three-variable law. -/

namespace Blotto
open MeasureTheory

theorem MergeFourInput.eq_of_data (i j : MergeFourInput) (hB : i.B = j.B) (h0 : i.l0 = j.l0)
    (h1 : i.l1 = j.l1) (h2 : i.l2 = j.l2) (h3 : i.l3 = j.l3) : i = j := by
  cases i
  cases j
  cases hB
  cases h0
  cases h1
  cases h2
  cases h3
  rfl

structure RationalMergeFourInput where
  B : ℚ
  l0 : ℚ
  l1 : ℚ
  l2 : ℚ
  l3 : ℚ
  l0_pos : 0 < l0
  l1_pos : 0 < l1
  l2_pos : 0 < l2
  l3_pos : 0 < l3
  pair_le : l0 + l1 ≤ B
  l2_le : l2 ≤ B
  l3_le : l3 ≤ B
  balance : l0 + l1 + l2 + l3 = 2 * B

theorem RationalMergeFourInput.eq_of_data (i j : RationalMergeFourInput)
    (hB : i.B = j.B) (h0 : i.l0 = j.l0) (h1 : i.l1 = j.l1)
    (h2 : i.l2 = j.l2) (h3 : i.l3 = j.l3) : i = j := by
  cases i
  cases j
  cases hB
  cases h0
  cases h1
  cases h2
  cases h3
  rfl

namespace RationalMergeFourInput

noncomputable def real (i : RationalMergeFourInput) : MergeFourInput where
  B := i.B
  l0 := i.l0
  l1 := i.l1
  l2 := i.l2
  l3 := i.l3
  l0_pos := by exact_mod_cast i.l0_pos
  l1_pos := by exact_mod_cast i.l1_pos
  l2_pos := by exact_mod_cast i.l2_pos
  l3_pos := by exact_mod_cast i.l3_pos
  pair_le := by exact_mod_cast i.pair_le
  l2_le := by exact_mod_cast i.l2_le
  l3_le := by exact_mod_cast i.l3_le
  balance := by exact_mod_cast i.balance

def childSpec (i : RationalMergeFourInput) : RationalThreeSpec where
  B := i.B
  a := i.l0 + i.l1
  d := i.l2
  c := i.l3
  p := 1
  B_pos := lt_of_lt_of_le i.l2_pos i.l2_le
  a_pos := add_pos i.l0_pos i.l1_pos
  d_pos := i.l2_pos
  c_pos := i.l3_pos
  p_pos := by norm_num
  a_le := i.pair_le
  d_le := i.l2_le
  c_le := i.l3_le
  p_le := le_rfl
  balance := by simpa using i.balance

theorem childSpec_real (i : RationalMergeFourInput) : i.childSpec.real = i.real.childSpec := by
  apply ThreeSpec.eq_of_data
  · rfl
  · exact Rat.cast_add _ _
  · rfl
  · rfl
  · exact Rat.cast_one

def segmentLottery (i : RationalMergeFourInput) : RationalSegmentLottery 4 9 :=
  i.childSpec.segmentLottery.mapped (RationalAffineAllocation.splitFirstTwo i.l0 i.l1)

theorem segmentLottery_law (i : RationalMergeFourInput) : i.segmentLottery.real.law = i.real.law := by
  unfold segmentLottery
  rw [RationalSegmentLottery.mapped_law, RationalThreeSpec.segmentLottery_real, i.childSpec_real]
  have hl : i.real.childSpec.segmentLottery.law = i.real.childSpec.law :=
    ProbabilityMeasure.toMeasure_injective i.real.childSpec.segmentLottery_law
  rw [hl]
  unfold MergeFourInput.law splitLaw
  congr 1
  exact funext (RationalAffineAllocation.splitFirstTwo_real i.l0 i.l1)

theorem segmentLottery_endpoints (i : RationalMergeFourInput) (slot : Fin 9) :
    FullBudget (i.B : ℝ) (i.segmentLottery.real.P slot) ∧ FullBudget (i.B : ℝ) (i.segmentLottery.real.Q slot) := by
  unfold segmentLottery
  rw [RationalSegmentLottery.mapped_real, RationalThreeSpec.segmentLottery_real, i.childSpec_real]
  constructor
  · change FullBudget (i.B : ℝ) ((RationalAffineAllocation.splitFirstTwo i.l0 i.l1).real.value (i.real.childSpec.segmentLottery.P slot))
    rw [RationalAffineAllocation.splitFirstTwo_real]
    exact splitFirstTwo_fullBudget i.real.l0_pos i.real.l1_pos (i.real.childSpec.segmentLottery_endpoints.1 slot)
  · change FullBudget (i.B : ℝ) ((RationalAffineAllocation.splitFirstTwo i.l0 i.l1).real.value (i.real.childSpec.segmentLottery.Q slot))
    rw [RationalAffineAllocation.splitFirstTwo_real]
    exact splitFirstTwo_fullBudget i.real.l0_pos i.real.l1_pos (i.real.childSpec.segmentLottery_endpoints.2 slot)

end RationalMergeFourInput

namespace RationalFourInput

def smallUniformInputReference (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) : RationalMergeFourInput where
  B := i.B
  l0 := i.scaleFraction * i.u
  l1 := i.scaleFraction * i.v
  l2 := i.scaleFraction * i.w
  l3 := i.ell
  l0_pos := i.scaled_uniform_bounds.1
  l1_pos := i.scaled_uniform_bounds.2.1
  l2_pos := i.scaled_uniform_bounds.2.2.1
  l3_pos := i.ell_pos
  pair_le := by
    have h := (i.real.smallUniformInput (i.smallCase_real hcase)).pair_le
    change i.real.scaleFraction * i.real.u + i.real.scaleFraction * i.real.v ≤ i.real.B at h
    rw [← i.scaleFraction_real] at h
    dsimp only [real] at h
    exact_mod_cast h
  l2_le := i.scaled_uniform_bounds.2.2.2.2.2.1
  l3_le := i.ell_le
  balance := i.scaled_uniform_bounds.2.2.2.2.2.2

def smallUniformInput (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) : RationalMergeFourInput :=
  let p := RationalFourParameterTable.prepare i
  { B := i.B
    l0 := p.scaleFraction * i.u
    l1 := p.scaleFraction * i.v
    l2 := p.scaleFraction * i.w
    l3 := i.ell
    l0_pos := by rw [p.scaleFraction_eq]; exact (i.smallUniformInputReference hcase).l0_pos
    l1_pos := by rw [p.scaleFraction_eq]; exact (i.smallUniformInputReference hcase).l1_pos
    l2_pos := by rw [p.scaleFraction_eq]; exact (i.smallUniformInputReference hcase).l2_pos
    l3_pos := i.ell_pos
    pair_le := by rw [p.scaleFraction_eq]; exact (i.smallUniformInputReference hcase).pair_le
    l2_le := by rw [p.scaleFraction_eq]; exact (i.smallUniformInputReference hcase).l2_le
    l3_le := i.ell_le
    balance := by rw [p.scaleFraction_eq]; exact (i.smallUniformInputReference hcase).balance }

theorem smallUniformInput_refines (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    i.smallUniformInput hcase = i.smallUniformInputReference hcase := by
  apply RationalMergeFourInput.eq_of_data
  · rfl
  · change (RationalFourParameterTable.prepare i).scaleFraction * i.u = _
    rw [RationalFourParameterTable.scaleFraction_eq]
    rfl
  · change (RationalFourParameterTable.prepare i).scaleFraction * i.v = _
    rw [RationalFourParameterTable.scaleFraction_eq]
    rfl
  · change (RationalFourParameterTable.prepare i).scaleFraction * i.w = _
    rw [RationalFourParameterTable.scaleFraction_eq]
    rfl
  · rfl

theorem smallUniformInput_real (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    (i.smallUniformInput hcase).real = i.real.smallUniformInput (i.smallCase_real hcase) := by
  rw [i.smallUniformInput_refines]
  apply MergeFourInput.eq_of_data
  · rfl
  · change ((i.scaleFraction * i.u : ℚ) : ℝ) = i.real.scaleFraction * (i.u : ℝ)
    rw [Rat.cast_mul, i.scaleFraction_real]
  · change ((i.scaleFraction * i.v : ℚ) : ℝ) = i.real.scaleFraction * (i.v : ℝ)
    rw [Rat.cast_mul, i.scaleFraction_real]
  · change ((i.scaleFraction * i.w : ℚ) : ℝ) = i.real.scaleFraction * (i.w : ℝ)
    rw [Rat.cast_mul, i.scaleFraction_real]
  · rfl

def smallUniformLottery (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) : RationalSegmentLottery 4 9 :=
  (i.smallUniformInput hcase).segmentLottery

theorem smallUniformLottery_law (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    (i.smallUniformLottery hcase).real.law = i.real.smallUniformLaw (i.smallCase_real hcase) := by
  rw [smallUniformLottery, RationalMergeFourInput.segmentLottery_law, i.smallUniformInput_real]
  rfl

end RationalFourInput
end Blotto
