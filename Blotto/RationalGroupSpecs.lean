import Blotto.RationalFourSpec
import Blotto.SmallGroupLaws

/-! Native rational inputs for the two/three-group terminal alternatives.
All input data and case tests remain rational; real views are proof-only. -/

namespace Blotto
open scoped BigOperators

structure RationalUniformGroupSpec (m : ℕ) where
  B : ℚ
  length : Fin m → ℚ
  B_pos : 0 < B
  length_pos : ∀ j, 0 < length j
  length_le : ∀ j, length j ≤ B
  balance : (∑ j, length j) = 2 * B

namespace RationalUniformGroupSpec

noncomputable def real {m : ℕ} (i : RationalUniformGroupSpec m) : UniformGroupSpec m where
  B := i.B
  length := fun j => i.length j
  B_pos := by exact_mod_cast i.B_pos
  length_pos := fun j => by exact_mod_cast i.length_pos j
  length_le := fun j => by exact_mod_cast i.length_le j
  balance := by exact_mod_cast i.balance

def threeInput (i : RationalUniformGroupSpec 3) : RationalThreeSpec where
  B := i.B
  a := i.length 0
  d := i.length 1
  c := i.length 2
  p := 1
  B_pos := i.B_pos
  a_pos := i.length_pos 0
  d_pos := i.length_pos 1
  c_pos := i.length_pos 2
  p_pos := by norm_num
  a_le := i.length_le 0
  d_le := i.length_le 1
  c_le := i.length_le 2
  p_le := le_rfl
  balance := by simpa [Fin.sum_univ_succ, add_assoc] using i.balance

theorem threeInput_real (i : RationalUniformGroupSpec 3) : i.threeInput.real = i.real.threeInput := by
  unfold threeInput RationalThreeSpec.real real UniformGroupSpec.threeInput
  simp only [Rat.cast_one]

theorem pair_lengths (i : RationalUniformGroupSpec 2) : ∀ j, i.length j = i.B := by
  intro j
  have he := i.real.pair_lengths j
  change (i.length j : ℝ) = (i.B : ℝ) at he
  exact_mod_cast he

end RationalUniformGroupSpec

structure RationalMixedGroupSpec (m : ℕ) where
  B : ℚ
  length : Fin m → ℚ
  ell : ℚ
  p : ℚ
  B_pos : 0 < B
  length_pos : ∀ j, 0 < length j
  length_le : ∀ j, length j ≤ B
  ell_pos : 0 < ell
  ell_le : ell ≤ B
  p_pos : 0 < p
  p_lt : p < 1
  balance : (∑ j, length j) + p * ell = 2 * B

namespace RationalMixedGroupSpec

noncomputable def real {m : ℕ} (i : RationalMixedGroupSpec m) : MixedGroupSpec m where
  B := i.B
  length := fun j => i.length j
  ell := i.ell
  p := i.p
  B_pos := by exact_mod_cast i.B_pos
  length_pos := fun j => by exact_mod_cast i.length_pos j
  length_le := fun j => by exact_mod_cast i.length_le j
  ell_pos := by exact_mod_cast i.ell_pos
  ell_le := by exact_mod_cast i.ell_le
  p_pos := by exact_mod_cast i.p_pos
  p_lt := by exact_mod_cast i.p_lt
  balance := by exact_mod_cast i.balance

def threeInput (i : RationalMixedGroupSpec 2) : RationalThreeSpec where
  B := i.B
  a := i.length 0
  d := i.length 1
  c := i.ell
  p := i.p
  B_pos := i.B_pos
  a_pos := i.length_pos 0
  d_pos := i.length_pos 1
  c_pos := i.ell_pos
  p_pos := i.p_pos
  a_le := i.length_le 0
  d_le := i.length_le 1
  c_le := i.ell_le
  p_le := le_of_lt i.p_lt
  balance := by simpa [Fin.sum_univ_succ, add_assoc] using i.balance

def fourInput (i : RationalMixedGroupSpec 3) : RationalFourSpec :=
  ⟨i.B, i.length, i.ell, i.p, i.length_pos, i.length_le, i.ell_pos, i.ell_le, i.p_pos, i.p_lt, i.balance⟩

theorem threeInput_real (i : RationalMixedGroupSpec 2) : i.threeInput.real = i.real.threeInput := rfl

theorem fourInput_real (i : RationalMixedGroupSpec 3) : i.fourInput.real = i.real.fourInput := rfl

end RationalMixedGroupSpec
end Blotto
