import Blotto.RationalNestedFamily
import Blotto.RationalThreeInput
import Blotto.NestedSecond
import Blotto.NestedThird

/-! Native numeric branch parameters for the remaining nested cases. The
translated uniform component is constructed only when its length is positive. -/

namespace Blotto

theorem ThreeInput.eq_of_data (i j : ThreeInput) (hB : i.B = j.B) (ha : i.a = j.a)
    (hd : i.d = j.d) (hc : i.c = j.c) (hp : i.p = j.p) : i = j := by
  cases i
  cases j
  cases hB
  cases ha
  cases hd
  cases hc
  cases hp
  rfl

namespace RationalNestedInput

def mirrorLength (i : RationalNestedInput) : ℚ := i.u + i.v - i.t
def secondAlpha (i : RationalNestedInput) : ℚ := i.mirrorLength * (i.h + i.t) / (i.t * (i.c - i.t))
def thirdAlpha (i : RationalNestedInput) : ℚ := i.v * (i.h + i.t) / (i.t * (i.h + i.v))

theorem mirrorLength_real (i : RationalNestedInput) : (i.mirrorLength : ℝ) = i.real.mirrorLength := by
  simp only [mirrorLength, Rat.cast_sub, Rat.cast_add, i.u_real, i.v_real]
  rfl

theorem secondAlpha_real (i : RationalNestedInput) : (i.secondAlpha : ℝ) = i.real.secondAlpha := by
  simp only [secondAlpha, Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_sub,
    i.mirrorLength_real, i.h_real]
  rfl

theorem thirdAlpha_real (i : RationalNestedInput) : (i.thirdAlpha : ℝ) = i.real.thirdAlpha := by
  simp only [thirdAlpha, Rat.cast_div, Rat.cast_mul, Rat.cast_add, i.v_real, i.h_real]
  rfl

theorem secondCase_real (i : RationalNestedInput) (htu : i.u ≤ i.t) : i.real.u ≤ i.real.t := by
  rw [← i.u_real]
  change (i.u : ℝ) ≤ (i.t : ℝ)
  exact_mod_cast htu

theorem mirrorLength_bounds (i : RationalNestedInput) (htu : i.u ≤ i.t) :
    0 < i.mirrorLength ∧ i.mirrorLength ≤ i.v ∧ i.mirrorLength ≤ i.t ∧ i.mirrorLength < i.u + i.v := by
  have hl := i.lengths
  dsimp [mirrorLength]
  constructor <;> try linarith [i.t_pos]
  constructor <;> try linarith [i.t_pos]
  constructor <;> linarith [i.t_pos]

theorem secondAlpha_bounds (i : RationalNestedInput) (htu : i.u ≤ i.t) :
    0 < i.secondAlpha ∧ i.secondAlpha ≤ 1 := by
  have h := i.real.secondAlpha_bounds (i.secondCase_real htu)
  rw [← i.secondAlpha_real] at h
  exact_mod_cast h

theorem thirdAlpha_bounds (i : RationalNestedInput) (hv : 0 < i.v) (hvt : i.v < i.t) :
    0 < i.thirdAlpha ∧ i.thirdAlpha < 1 := by
  have hvR : 0 < i.real.v := by rw [← i.v_real]; exact_mod_cast hv
  have hvtR : i.real.v < i.real.t := by
    rw [← i.v_real]; change (i.v : ℝ) < (i.t : ℝ); exact_mod_cast hvt
  have h := i.real.thirdAlpha_bounds hvR hvtR
  rw [← i.thirdAlpha_real] at h
  exact_mod_cast h

def secondUniformInput (i : RationalNestedInput) (htu : i.u ≤ i.t)
    (hTt : i.mirrorLength < i.t) : RationalThreeInput where
  B := i.M - i.mirrorLength
  a := i.a
  d := i.d
  c := i.t - i.mirrorLength
  p := 1
  B_pos := by have hv := (i.mirrorLength_bounds htu).2.1; dsimp [v] at hv; linarith [i.d_pos]
  a_pos := i.a_pos
  d_pos := i.d_pos
  c_pos := sub_pos.mpr hTt
  p_pos := by norm_num
  a_le := by
    have hu := ((i.mirrorLength_bounds htu).2.1).trans i.lengths.2.1
    dsimp [u] at hu
    linarith
  d_le := by have hv := (i.mirrorLength_bounds htu).2.1; dsimp [v] at hv; linarith
  c_le := by linarith [i.t_lt, i.c_le]
  p_le := le_rfl
  ordered := i.ordered
  balance := by dsimp [mirrorLength, u, v]; ring

theorem secondUniformInput_real (i : RationalNestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) :
    (i.secondUniformInput htu hTt).real = i.real.secondUniformInput (i.secondCase_real htu)
      (by rw [← i.mirrorLength_real]; change (i.mirrorLength : ℝ) < (i.t : ℝ); exact_mod_cast hTt) := by
  apply ThreeInput.eq_of_data
  · change ((i.M - i.mirrorLength : ℚ) : ℝ) = (i.M : ℝ) - i.real.mirrorLength
    rw [Rat.cast_sub, i.mirrorLength_real]
  · rfl
  · rfl
  · change ((i.t - i.mirrorLength : ℚ) : ℝ) = (i.t : ℝ) - i.real.mirrorLength
    rw [Rat.cast_sub, i.mirrorLength_real]
  · exact Rat.cast_one

end RationalNestedInput
end Blotto
