import Blotto.RationalNestedProgram
import Blotto.RationalLotterySwap

/-! Native nested inputs with endpoint mixture weights and either coordinate
order. Positive short/long lengths retain the existing NestedSpec scope. -/

namespace Blotto
open MeasureTheory

theorem ThreeSpec.eq_of_data (i j : ThreeSpec) (hB : i.B = j.B) (ha : i.a = j.a)
    (hd : i.d = j.d) (hc : i.c = j.c) (hp : i.p = j.p) : i = j := by
  cases i
  cases j
  cases hB
  cases ha
  cases hd
  cases hc
  cases hp
  rfl

structure RationalNestedSpec where
  M : ℚ
  a : ℚ
  d : ℚ
  c : ℚ
  t : ℚ
  q : ℚ
  a_pos : 0 < a
  d_pos : 0 < d
  c_pos : 0 < c
  t_pos : 0 < t
  t_lt : t < c
  q_nonneg : 0 ≤ q
  q_le : q ≤ 1
  a_le : a ≤ M
  d_le : d ≤ M
  c_le : c ≤ M
  balance : a + d + q * t + (1 - q) * c = 2 * M

namespace RationalNestedSpec

noncomputable def real (i : RationalNestedSpec) : NestedSpec where
  M := i.M
  a := i.a
  d := i.d
  c := i.c
  t := i.t
  q := i.q
  a_pos := by exact_mod_cast i.a_pos
  d_pos := by exact_mod_cast i.d_pos
  c_pos := by exact_mod_cast i.c_pos
  t_pos := by exact_mod_cast i.t_pos
  t_lt := by exact_mod_cast i.t_lt
  q_nonneg := by exact_mod_cast i.q_nonneg
  q_le := by exact_mod_cast i.q_le
  a_le := by exact_mod_cast i.a_le
  d_le := by exact_mod_cast i.d_le
  c_le := by exact_mod_cast i.c_le
  balance := by exact_mod_cast i.balance

def longInput (i : RationalNestedSpec) (hq : i.q = 0) : RationalThreeSpec where
  B := i.M
  a := i.a
  d := i.d
  c := i.c
  p := 1
  B_pos := lt_of_lt_of_le i.a_pos i.a_le
  a_pos := i.a_pos
  d_pos := i.d_pos
  c_pos := i.c_pos
  p_pos := by norm_num
  a_le := i.a_le
  d_le := i.d_le
  c_le := i.c_le
  p_le := le_rfl
  balance := by simpa [hq] using i.balance

def shortInput (i : RationalNestedSpec) (hq : i.q = 1) : RationalThreeSpec where
  B := i.M
  a := i.a
  d := i.d
  c := i.t
  p := 1
  B_pos := lt_of_lt_of_le i.a_pos i.a_le
  a_pos := i.a_pos
  d_pos := i.d_pos
  c_pos := i.t_pos
  p_pos := by norm_num
  a_le := i.a_le
  d_le := i.d_le
  c_le := (le_of_lt i.t_lt).trans i.c_le
  p_le := le_rfl
  balance := by simpa [hq] using i.balance

def interiorInput (i : RationalNestedSpec) (hq0 : 0 < i.q) (hq1 : i.q < 1) : RationalNestedInput where
  M := i.M
  a := min i.a i.d
  d := max i.a i.d
  c := i.c
  t := i.t
  q := i.q
  a_pos := lt_min i.a_pos i.d_pos
  d_pos := lt_of_lt_of_le i.a_pos (le_max_left _ _)
  c_pos := i.c_pos
  t_pos := i.t_pos
  t_lt := i.t_lt
  q_pos := hq0
  q_lt := hq1
  a_le := (min_le_left _ _).trans i.a_le
  d_le := max_le i.a_le i.d_le
  c_le := i.c_le
  ordered := min_le_max
  balance := by rw [min_add_max]; exact i.balance

theorem longInput_real (i : RationalNestedSpec) (hq : i.q = 0) :
    (i.longInput hq).real = i.real.longInput (by change (i.q : ℝ) = 0; exact_mod_cast hq) := by
  apply ThreeSpec.eq_of_data <;> first | rfl | exact Rat.cast_one

theorem shortInput_real (i : RationalNestedSpec) (hq : i.q = 1) :
    (i.shortInput hq).real = i.real.shortInput (by change (i.q : ℝ) = 1; exact_mod_cast hq) := by
  apply ThreeSpec.eq_of_data <;> first | rfl | exact Rat.cast_one

theorem interiorInput_real (i : RationalNestedSpec) (hq0 : 0 < i.q) (hq1 : i.q < 1) :
    (i.interiorInput hq0 hq1).real = i.real.interiorInput
      (by change (0 : ℝ) < (i.q : ℝ); exact_mod_cast hq0)
      (by change (i.q : ℝ) < 1; exact_mod_cast hq1) := by
  apply NestedInput.eq_of_data
  · rfl
  · change ((min i.a i.d : ℚ) : ℝ) = min (i.a : ℝ) (i.d : ℝ)
    exact Rat.cast_min _ _
  · change ((max i.a i.d : ℚ) : ℝ) = max (i.a : ℝ) (i.d : ℝ)
    exact Rat.cast_max _ _
  · rfl
  · rfl
  · rfl

def profile (i : RationalNestedSpec) (K : ℕ) (outerBits : Fin K → Bool) : RationalSegmentLottery 3 18 :=
  if hq0 : i.q = 0 then (i.longInput hq0).segmentLottery.padRight 9 0
  else if hq1 : i.q = 1 then (i.shortInput hq1).segmentLottery.padRight 9 0
  else
    let j := i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)
    if i.a ≤ i.d then j.profile K outerBits else (j.profile K outerBits).swapFirst

theorem profile_endpoints (i : RationalNestedSpec) (K : ℕ) (outerBits : Fin K → Bool) (slot : Fin 18) :
    FullBudget (i.M : ℝ) ((i.profile K outerBits).real.P slot) ∧
      FullBudget (i.M : ℝ) ((i.profile K outerBits).real.Q slot) := by
  unfold profile
  split_ifs with hq0 hq1 had
  · apply RationalSegmentLottery.padRight_endpoints
    intro edge
    rw [RationalThreeSpec.segmentLottery_real]
    exact ⟨(i.longInput hq0).real.segmentLottery_endpoints.1 edge, (i.longInput hq0).real.segmentLottery_endpoints.2 edge⟩
  · apply RationalSegmentLottery.padRight_endpoints
    intro edge
    rw [RationalThreeSpec.segmentLottery_real]
    exact ⟨(i.shortInput hq1).real.segmentLottery_endpoints.1 edge, (i.shortInput hq1).real.segmentLottery_endpoints.2 edge⟩
  · exact (i.interiorInput _ _).profile_endpoints K outerBits slot
  · apply RationalSegmentLottery.swapFirst_endpoints
    exact (i.interiorInput _ _).profile_endpoints K outerBits

end RationalNestedSpec
end Blotto
