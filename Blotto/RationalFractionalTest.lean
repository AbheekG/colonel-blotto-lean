import Blotto.RationalResourceArray

/-! A source fractional test caches its resource read and consults the cap
only on the positive branch. Its Boolean result is the retained strict test.
Prices count actual operand copies/comparisons; reader implementations and
address/control/container costs are separate. -/

namespace Blotto

def rationalFractionalAt {α : Type*} (L r : α → ℚ) (j : α) : Bool :=
  let value := r j
  if 0 < value then decide (value < L j) else false

theorem rationalFractionalAt_eq_decide {α : Type*} (L r : α → ℚ) (j : α) :
    rationalFractionalAt L r j = decide (0 < r j ∧ r j < L j) := by
  by_cases hp : 0 < r j <;> simp [rationalFractionalAt, hp]

@[simp] theorem rationalFractionalAt_function {α : Type*} (L r : α → ℚ) :
    rationalFractionalAt L r = (fun j => decide (0 < r j ∧ r j < L j)) :=
  funext (rationalFractionalAt_eq_decide L r)


def rationalFractionalRamWork {α : Type*} (_L r : α → ℚ) (j : α) : ℕ :=
  if 0 < r j then 5 else 2

theorem rationalFractionalRamWork_bound {α : Type*} (L r : α → ℚ) (j : α) :
    rationalFractionalRamWork L r j ≤ 5 := by unfold rationalFractionalRamWork; split_ifs <;> omega


end Blotto
