import Blotto.RationalFourInput
import Blotto.FourGluingDescriptor
import Blotto.RationalFourParameterTable
import Blotto.RationalFourFactoryEquality

/-! Native auxiliary three-variable inputs of the four-variable gluing
case. All bounds and the auxiliary budget sum retain the real construction. -/

namespace Blotto.RationalFourInput

theorem auxLength_pos (i : RationalFourInput) : 0 < i.auxLength := by
  have h := i.real.auxLength_pos
  rw [← i.auxLength_real] at h
  exact_mod_cast h

theorem auxiliary_budget_sum (i : RationalFourInput) : i.firstBudget + i.secondBudget - i.auxLength = i.B := by
  dsimp [firstBudget, secondBudget]
  linarith [i.balance]

def gluingFirstSpecReference (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : RationalThreeSpec where
  B := i.firstBudget
  a := i.u
  d := i.v
  c := i.auxLength
  p := 1
  B_pos := (i.auxiliary_budget_bounds hcase).1
  a_pos := i.u_pos
  d_pos := i.lengths_positive.1
  c_pos := i.auxLength_pos
  p_pos := by norm_num
  a_le := (i.auxiliary_budget_bounds hcase).2.1
  d_le := (i.auxiliary_budget_bounds hcase).2.2.1
  c_le := (i.auxiliary_budget_bounds hcase).2.2.2.1
  p_le := le_rfl
  balance := by dsimp [firstBudget]; ring

def gluingSecondSpecReference (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : RationalThreeSpec where
  B := i.secondBudget
  a := i.auxLength
  d := i.w
  c := i.ell
  p := i.p
  B_pos := (i.auxiliary_budget_bounds hcase).2.2.2.2.1
  a_pos := i.auxLength_pos
  d_pos := i.lengths_positive.2.1
  c_pos := i.ell_pos
  p_pos := i.p_pos
  a_le := (i.auxiliary_budget_bounds hcase).2.2.2.2.2.1
  d_le := (i.auxiliary_budget_bounds hcase).2.2.2.2.2.2.1
  c_le := (i.auxiliary_budget_bounds hcase).2.2.2.2.2.2.2
  p_le := le_of_lt i.p_lt
  balance := by dsimp [secondBudget]; ring

def gluingFirstSpec (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : RationalThreeSpec :=
  let p := RationalFourParameterTable.prepare i
  { B := p.firstBudget
    a := i.u
    d := i.v
    c := p.auxLength
    p := 1
    B_pos := by rw [p.firstBudget_eq]; exact (i.gluingFirstSpecReference hcase).B_pos
    a_pos := i.u_pos
    d_pos := i.lengths_positive.1
    c_pos := by rw [p.auxLength_eq]; exact i.auxLength_pos
    p_pos := by norm_num
    a_le := by rw [p.firstBudget_eq]; exact (i.gluingFirstSpecReference hcase).a_le
    d_le := by rw [p.firstBudget_eq]; exact (i.gluingFirstSpecReference hcase).d_le
    c_le := by rw [p.firstBudget_eq, p.auxLength_eq]; exact (i.gluingFirstSpecReference hcase).c_le
    p_le := le_rfl
    balance := by rw [p.firstBudget_eq, p.auxLength_eq]; exact (i.gluingFirstSpecReference hcase).balance }

theorem gluingFirstSpec_refines (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    i.gluingFirstSpec hcase = i.gluingFirstSpecReference hcase := by
  apply RationalThreeSpec.eq_of_data
  · exact (RationalFourParameterTable.prepare i).firstBudget_eq
  · rfl
  · rfl
  · exact (RationalFourParameterTable.prepare i).auxLength_eq
  · rfl

def gluingSecondSpec (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) : RationalThreeSpec :=
  let p := RationalFourParameterTable.prepare i
  { B := p.secondBudget
    a := p.auxLength
    d := i.w
    c := i.ell
    p := i.p
    B_pos := by rw [p.secondBudget_eq]; exact (i.gluingSecondSpecReference hcase).B_pos
    a_pos := by rw [p.auxLength_eq]; exact i.auxLength_pos
    d_pos := i.lengths_positive.2.1
    c_pos := i.ell_pos
    p_pos := i.p_pos
    a_le := by rw [p.secondBudget_eq, p.auxLength_eq]; exact (i.gluingSecondSpecReference hcase).a_le
    d_le := by rw [p.secondBudget_eq]; exact (i.gluingSecondSpecReference hcase).d_le
    c_le := by rw [p.secondBudget_eq]; exact (i.gluingSecondSpecReference hcase).c_le
    p_le := i.p_lt.le
    balance := by rw [p.secondBudget_eq, p.auxLength_eq]; exact (i.gluingSecondSpecReference hcase).balance }

theorem gluingSecondSpec_refines (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    i.gluingSecondSpec hcase = i.gluingSecondSpecReference hcase := by
  apply RationalThreeSpec.eq_of_data
  · exact (RationalFourParameterTable.prepare i).secondBudget_eq
  · exact (RationalFourParameterTable.prepare i).auxLength_eq
  · rfl
  · rfl
  · rfl

theorem gluingFirstSpec_real (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    (i.gluingFirstSpec hcase).real = i.real.gluingFirstSpec (i.gluingCase_real hcase) := by
  rw [i.gluingFirstSpec_refines]
  apply ThreeSpec.eq_of_data
  · exact i.firstBudget_real
  · rfl
  · rfl
  · exact i.auxLength_real
  · exact Rat.cast_one

theorem gluingSecondSpec_real (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    (i.gluingSecondSpec hcase).real = i.real.gluingSecondSpec (i.gluingCase_real hcase) := by
  rw [i.gluingSecondSpec_refines]
  apply ThreeSpec.eq_of_data
  · exact i.secondBudget_real
  · exact i.auxLength_real
  · rfl
  · rfl
  · rfl

end Blotto.RationalFourInput
