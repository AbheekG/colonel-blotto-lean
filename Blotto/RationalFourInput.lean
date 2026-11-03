import Blotto.RationalNestedSpecProgram
import Blotto.FourReflectionRecovery

/-! Native rational inputs and numeric parameters of the ordered four-variable
construction. Exact cast identities preserve both original branch conditions. -/

namespace Blotto
open scoped BigOperators

theorem FourInput.eq_of_data (i j : FourInput) (hB : i.B = j.B) (hu : i.u = j.u)
    (hv : i.v = j.v) (hw : i.w = j.w) (he : i.ell = j.ell) (hp : i.p = j.p) : i = j := by
  cases i
  cases j
  cases hB
  cases hu
  cases hv
  cases hw
  cases he
  cases hp
  rfl

structure RationalFourInput where
  B : ℚ
  u : ℚ
  v : ℚ
  w : ℚ
  ell : ℚ
  p : ℚ
  u_pos : 0 < u
  uv : u ≤ v
  vw : v ≤ w
  ell_pos : 0 < ell
  p_pos : 0 < p
  p_lt : p < 1
  w_le : w ≤ B
  ell_le : ell ≤ B
  balance : u + v + w + p * ell = 2 * B

namespace RationalFourInput

noncomputable def real (i : RationalFourInput) : FourInput where
  B := i.B
  u := i.u
  v := i.v
  w := i.w
  ell := i.ell
  p := i.p
  u_pos := by exact_mod_cast i.u_pos
  uv := by exact_mod_cast i.uv
  vw := by exact_mod_cast i.vw
  ell_pos := by exact_mod_cast i.ell_pos
  p_pos := by exact_mod_cast i.p_pos
  p_lt := by exact_mod_cast i.p_lt
  w_le := by exact_mod_cast i.w_le
  ell_le := by exact_mod_cast i.ell_le
  balance := by exact_mod_cast i.balance

def S (i : RationalFourInput) : ℚ := i.u + i.v + i.w
def auxLength (i : RationalFourInput) : ℚ :=
  max (max (max (i.v - i.u) (i.w - i.p * i.ell)) ((2 - i.p) * i.ell - i.w)) 0
def firstBudget (i : RationalFourInput) : ℚ := (i.u + i.v + i.auxLength) / 2
def secondBudget (i : RationalFourInput) : ℚ := (i.auxLength + i.w + i.p * i.ell) / 2
def shortFraction (i : RationalFourInput) : ℚ := (1 - i.p) * i.ell / i.S
def scaleFraction (i : RationalFourInput) : ℚ := 1 - i.shortFraction
def nestedProbability (i : RationalFourInput) : ℚ := i.p * i.ell / (i.S - (1 - i.p) * i.ell)
def reflectedBudget (i : RationalFourInput) : ℚ := (i.S - i.p * i.ell) / 2
def originalLengths (i : RationalFourInput) : Fin 3 → ℚ := ![i.u, i.v, i.w]

theorem S_real (i : RationalFourInput) : (i.S : ℝ) = i.real.S := by simp [S, real, FourInput.S]
theorem auxLength_real (i : RationalFourInput) : (i.auxLength : ℝ) = i.real.auxLength := by
  simp [auxLength, real, FourInput.auxLength]
theorem firstBudget_real (i : RationalFourInput) : (i.firstBudget : ℝ) = i.real.firstBudget := by
  simp only [firstBudget, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, i.auxLength_real]
  rfl
theorem secondBudget_real (i : RationalFourInput) : (i.secondBudget : ℝ) = i.real.secondBudget := by
  simp only [secondBudget, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, i.auxLength_real]
  rfl
theorem shortFraction_real (i : RationalFourInput) : (i.shortFraction : ℝ) = i.real.shortFraction := by
  simp only [shortFraction, Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_one, i.S_real]
  rfl
theorem scaleFraction_real (i : RationalFourInput) : (i.scaleFraction : ℝ) = i.real.scaleFraction := by
  simp only [scaleFraction, Rat.cast_sub, Rat.cast_one, i.shortFraction_real]
  rfl
theorem nestedProbability_real (i : RationalFourInput) : (i.nestedProbability : ℝ) = i.real.nestedProbability := by
  simp only [nestedProbability, Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_one, i.S_real]
  rfl
theorem reflectedBudget_real (i : RationalFourInput) : (i.reflectedBudget : ℝ) = i.real.reflectedBudget := by
  simp only [reflectedBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, i.S_real]
  rfl
theorem originalLengths_real (i : RationalFourInput) :
    (fun j => (i.originalLengths j : ℝ)) = i.real.originalLengths := by
  funext j
  fin_cases j <;> rfl

theorem lengths_positive (i : RationalFourInput) : 0 < i.v ∧ 0 < i.w ∧ 0 < i.B ∧ 0 < i.S := by
  have hv := lt_of_lt_of_le i.u_pos i.uv
  have hw := lt_of_lt_of_le hv i.vw
  exact ⟨hv, hw, lt_of_lt_of_le hw i.w_le, by dsimp [S]; linarith [i.u_pos]⟩

theorem shortFraction_bounds (i : RationalFourInput) : 0 < i.shortFraction ∧ i.shortFraction < 1 := by
  have h := i.real.shortFraction_bounds
  rw [← i.shortFraction_real] at h
  exact_mod_cast h

theorem scaleFraction_bounds (i : RationalFourInput) : 0 < i.scaleFraction ∧ i.scaleFraction < 1 := by
  have h := i.real.scaleFraction_bounds
  rw [← i.scaleFraction_real] at h
  exact_mod_cast h

theorem nestedProbability_bounds (i : RationalFourInput) : 0 < i.nestedProbability ∧ i.nestedProbability < 1 := by
  have h := i.real.nestedProbability_bounds
  rw [← i.nestedProbability_real] at h
  exact_mod_cast h

theorem smallCase_real (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    i.real.w < (1 - i.real.p) * i.real.ell := by
  change (i.w : ℝ) < (1 - (i.p : ℝ)) * (i.ell : ℝ)
  exact_mod_cast hcase

theorem gluingCase_real (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    (1 - i.real.p) * i.real.ell ≤ i.real.w := by
  change (1 - (i.p : ℝ)) * (i.ell : ℝ) ≤ (i.w : ℝ)
  exact_mod_cast hcase

theorem scaled_uniform_bounds (i : RationalFourInput) :
    0 < i.scaleFraction * i.u ∧ 0 < i.scaleFraction * i.v ∧ 0 < i.scaleFraction * i.w ∧
      i.scaleFraction * i.u ≤ i.B ∧ i.scaleFraction * i.v ≤ i.B ∧ i.scaleFraction * i.w ≤ i.B ∧
      i.scaleFraction * i.u + i.scaleFraction * i.v + i.scaleFraction * i.w + i.ell = 2 * i.B := by
  have h := i.real.scaled_uniform_bounds
  rw [← i.scaleFraction_real] at h
  dsimp only [real] at h
  exact_mod_cast h

theorem reflected_budget_bounds (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    i.w < i.reflectedBudget ∧ i.reflectedBudget = i.S - i.B := by
  have h := i.real.reflected_budget_bounds (i.smallCase_real hcase)
  rw [← i.reflectedBudget_real, ← i.S_real] at h
  dsimp only [real] at h
  exact_mod_cast h

theorem auxiliary_budget_bounds (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    0 < i.firstBudget ∧ i.u ≤ i.firstBudget ∧ i.v ≤ i.firstBudget ∧ i.auxLength ≤ i.firstBudget ∧
      0 < i.secondBudget ∧ i.auxLength ≤ i.secondBudget ∧ i.w ≤ i.secondBudget ∧ i.ell ≤ i.secondBudget := by
  have h := i.real.auxiliary_budget_bounds (i.gluingCase_real hcase)
  rw [← i.firstBudget_real, ← i.secondBudget_real, ← i.auxLength_real] at h
  dsimp only [real] at h
  exact_mod_cast h

theorem originalLengths_pos (i : RationalFourInput) (j : Fin 3) : 0 < i.originalLengths j := by
  fin_cases j
  · exact i.u_pos
  · exact i.lengths_positive.1
  · exact i.lengths_positive.2.1

theorem originalLengths_sum (i : RationalFourInput) : (∑ j, i.originalLengths j) = i.S := by
  simp [originalLengths, S, Fin.sum_univ_succ, add_assoc]

end RationalFourInput
end Blotto
