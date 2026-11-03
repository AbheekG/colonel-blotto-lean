import Blotto.RationalPRGInput
import Blotto.RationalLottoProgram

/-! Rational normalized PRG inputs supply both full native controllers.
No partition is supplied. Budget holds on every path; the final global
midpoint/Nash and all input/encoding/cost ledgers remain separate obligations. -/

namespace Blotto
open scoped BigOperators

theorem LottoResourceSystem.eq_of_data {n : ℕ} (i j : LottoResourceSystem n) (hB : i.B = j.B)
    (hL : i.length = j.length) (hr : i.initial = j.initial) : i = j := by
  cases i
  cases j
  cases hB
  cases hL
  cases hr
  rfl

namespace RationalPRGInput

theorem lengths_pos {n : ℕ} (i : RationalPRGInput n) (j : Fin n) : 0 < i.lengths j := by
  unfold lengths
  exact mul_pos (by norm_num) (i.positive j)

theorem lengths_sum {n : ℕ} (i : RationalPRGInput n) : (∑ j, i.lengths j) = 2 := by
  simp only [lengths, ← Finset.mul_sum, i.normalized, mul_one]

def richNativeSystem {n : ℕ} (i : RationalPRGInput n) : RationalLottoResourceSystem n where
  B := 1
  length := i.lengths
  initial := i.richInitial
  B_pos := by norm_num
  length_pos := i.lengths_pos
  length_le := fun j => (i.small_fields j).trans i.b_le
  initial_box := fun j => ⟨le_of_lt (i.lengths_pos j), le_rfl⟩
  initial_sum := by simpa only [richInitial, mul_one] using i.lengths_sum

def poorNativeSystem {n : ℕ} (i : RationalPRGInput n) : RationalLottoResourceSystem n where
  B := i.b
  length := i.lengths
  initial := i.poorInitial
  B_pos := i.b_pos
  length_pos := i.lengths_pos
  length_le := i.small_fields
  initial_box := fun j => ⟨mul_nonneg (le_of_lt i.b_pos) (le_of_lt (i.lengths_pos j)),
    mul_le_of_le_one_left (le_of_lt (i.lengths_pos j)) i.b_le⟩
  initial_sum := by
    simp only [poorInitial, ← Finset.mul_sum, i.lengths_sum]
    ring

theorem richNativeSystem_real {n : ℕ} (i : RationalPRGInput n) : i.richNativeSystem.real = i.real.richSystem := by
  apply LottoResourceSystem.eq_of_data
  · simp [richNativeSystem, RationalLottoResourceSystem.real, PRGInput.richSystem]
  · exact i.lengths_real
  · exact i.richInitial_real

theorem poorNativeSystem_real {n : ℕ} (i : RationalPRGInput n) : i.poorNativeSystem.real = i.real.poorSystem := by
  apply LottoResourceSystem.eq_of_data
  · rfl
  · exact i.lengths_real
  · exact i.poorInitial_real

def richProgram {n : ℕ} (i : RationalPRGInput n) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    RationalAllocationProgram n (n - 1 + 80) := i.richNativeSystem.program K outerBits scalarBits

def poorProgram {n : ℕ} (i : RationalPRGInput n) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    RationalAllocationProgram n (n - 1 + 80) := i.poorNativeSystem.program K outerBits scalarBits

theorem richProgram_fullBudget {n : ℕ} (i : RationalPRGInput n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    FullBudget 1 (fun j => ((i.richProgram K outerBits scalarBits).sample R choiceBits j : ℝ)) := by
  have h := i.richNativeSystem.program_sample_fullBudget K R outerBits scalarBits choiceBits
  have he : (i.richNativeSystem.B : ℝ) = 1 := by
    change ((1 : ℚ) : ℝ) = 1
    norm_num
  rw [he] at h
  exact h

theorem poorProgram_fullBudget {n : ℕ} (i : RationalPRGInput n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    FullBudget (i.b : ℝ) (fun j => ((i.poorProgram K outerBits scalarBits).sample R choiceBits j : ℝ)) :=
  i.poorNativeSystem.program_sample_fullBudget K R outerBits scalarBits choiceBits

end RationalPRGInput
end Blotto
