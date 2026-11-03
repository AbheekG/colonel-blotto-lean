import Blotto.RealFourParameterTable
import Blotto.FourGluing
import Blotto.RationalMergeFour
import Blotto.RationalNestedResourceSystem

/-! Counted scalar-table reads construct the actual parent, merged-uniform
and reflected-resource inputs. Proof fields use exact numerical refinement. -/

namespace Blotto.RealFourParameterTable

noncomputable def gluingFirstSpec {i : FourInput} (p : RealFourParameterTable i)
    (hcase : (1 - i.p) * i.ell ≤ i.w) : ThreeSpec where
  B := p.firstBudget
  a := i.u
  d := i.v
  c := p.auxLength
  p := 1
  B_pos := by rw [p.firstBudget_eq]; exact (i.gluingFirstSpec hcase).B_pos
  a_pos := i.u_pos
  d_pos := i.lengths_positive.1
  c_pos := by rw [p.auxLength_eq]; exact i.auxLength_pos
  p_pos := by norm_num
  a_le := by rw [p.firstBudget_eq]; exact (i.gluingFirstSpec hcase).a_le
  d_le := by rw [p.firstBudget_eq]; exact (i.gluingFirstSpec hcase).d_le
  c_le := by rw [p.firstBudget_eq, p.auxLength_eq]; exact (i.gluingFirstSpec hcase).c_le
  p_le := le_rfl
  balance := by rw [p.firstBudget_eq, p.auxLength_eq]; exact (i.gluingFirstSpec hcase).balance

theorem gluingFirstSpec_eq {i : FourInput} (p : RealFourParameterTable i)
    (hcase : (1 - i.p) * i.ell ≤ i.w) : p.gluingFirstSpec hcase = i.gluingFirstSpec hcase := by
  apply ThreeSpec.eq_of_data
  · exact p.firstBudget_eq
  · rfl
  · rfl
  · exact p.auxLength_eq
  · rfl

noncomputable def gluingSecondSpec {i : FourInput} (p : RealFourParameterTable i)
    (hcase : (1 - i.p) * i.ell ≤ i.w) : ThreeSpec where
  B := p.secondBudget
  a := p.auxLength
  d := i.w
  c := i.ell
  p := i.p
  B_pos := by rw [p.secondBudget_eq]; exact (i.gluingSecondSpec hcase).B_pos
  a_pos := by rw [p.auxLength_eq]; exact i.auxLength_pos
  d_pos := i.lengths_positive.2.1
  c_pos := i.ell_pos
  p_pos := i.p_pos
  a_le := by rw [p.secondBudget_eq, p.auxLength_eq]; exact (i.gluingSecondSpec hcase).a_le
  d_le := by rw [p.secondBudget_eq]; exact (i.gluingSecondSpec hcase).d_le
  c_le := by rw [p.secondBudget_eq]; exact (i.gluingSecondSpec hcase).c_le
  p_le := i.p_lt.le
  balance := by rw [p.secondBudget_eq, p.auxLength_eq]; exact (i.gluingSecondSpec hcase).balance

theorem gluingSecondSpec_eq {i : FourInput} (p : RealFourParameterTable i)
    (hcase : (1 - i.p) * i.ell ≤ i.w) : p.gluingSecondSpec hcase = i.gluingSecondSpec hcase := by
  apply ThreeSpec.eq_of_data
  · exact p.secondBudget_eq
  · exact p.auxLength_eq
  · rfl
  · rfl
  · rfl

noncomputable def smallUniformInput {i : FourInput} (p : RealFourParameterTable i)
    (hcase : i.w < (1 - i.p) * i.ell) : MergeFourInput where
  B := i.B
  l0 := p.scaleFraction * i.u
  l1 := p.scaleFraction * i.v
  l2 := p.scaleFraction * i.w
  l3 := i.ell
  l0_pos := by rw [p.scaleFraction_eq]; exact (i.smallUniformInput hcase).l0_pos
  l1_pos := by rw [p.scaleFraction_eq]; exact (i.smallUniformInput hcase).l1_pos
  l2_pos := by rw [p.scaleFraction_eq]; exact (i.smallUniformInput hcase).l2_pos
  l3_pos := i.ell_pos
  pair_le := by rw [p.scaleFraction_eq]; exact (i.smallUniformInput hcase).pair_le
  l2_le := by rw [p.scaleFraction_eq]; exact (i.smallUniformInput hcase).l2_le
  l3_le := i.ell_le
  balance := by rw [p.scaleFraction_eq]; exact (i.smallUniformInput hcase).balance

theorem smallUniformInput_eq {i : FourInput} (p : RealFourParameterTable i)
    (hcase : i.w < (1 - i.p) * i.ell) : p.smallUniformInput hcase = i.smallUniformInput hcase := by
  apply MergeFourInput.eq_of_data
  · rfl
  · change p.scaleFraction * i.u = i.scaleFraction * i.u; rw [p.scaleFraction_eq]
  · change p.scaleFraction * i.v = i.scaleFraction * i.v; rw [p.scaleFraction_eq]
  · change p.scaleFraction * i.w = i.scaleFraction * i.w; rw [p.scaleFraction_eq]
  · rfl

noncomputable def reflectedResourceSystem {i : FourInput} (p : RealFourParameterTable i)
    (hcase : i.w < (1 - i.p) * i.ell) : NestedResourceSystem where
  M := p.reflectedBudget
  long := i.originalLengths
  short := fun j => p.shortFraction * i.originalLengths j
  initial := fun j => p.nestedProbability * p.scaleFraction * i.originalLengths j
  short_pos := by intro j; rw [p.shortFraction_eq]; exact (i.reflectedResourceSystem hcase).short_pos j
  short_lt := by intro j; rw [p.shortFraction_eq]; exact (i.reflectedResourceSystem hcase).short_lt j
  long_le := by intro j; rw [p.reflectedBudget_eq]; exact (i.reflectedResourceSystem hcase).long_le j
  initial_box := by
    intro j
    rw [p.nestedProbability_eq, p.scaleFraction_eq, p.shortFraction_eq]
    exact (i.reflectedResourceSystem hcase).initial_box j
  initial_mean := by
    rw [p.nestedProbability_eq, p.scaleFraction_eq, p.reflectedBudget_eq]
    exact (i.reflectedResourceSystem hcase).initial_mean

theorem reflectedResourceSystem_eq {i : FourInput} (p : RealFourParameterTable i)
    (hcase : i.w < (1 - i.p) * i.ell) : p.reflectedResourceSystem hcase = i.reflectedResourceSystem hcase := by
  apply NestedResourceSystem.eq_of_data
  · exact p.reflectedBudget_eq
  · rfl
  · funext j; change p.shortFraction * i.originalLengths j = _; rw [p.shortFraction_eq]; rfl
  · funext j
    change p.nestedProbability * p.scaleFraction * i.originalLengths j = _
    rw [p.nestedProbability_eq, p.scaleFraction_eq]
    rfl

end Blotto.RealFourParameterTable
