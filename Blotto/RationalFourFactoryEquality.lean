import Blotto.RationalNestedResourceSystem
import Blotto.RationalFourInput

/-! Numeric data equality identifies native factory records. -/

namespace Blotto

theorem RationalThreeSpec.eq_of_data (i j : RationalThreeSpec) (hB : i.B = j.B)
    (ha : i.a = j.a) (hd : i.d = j.d) (hc : i.c = j.c) (hp : i.p = j.p) : i = j := by
  cases i
  cases j
  cases hB
  cases ha
  cases hd
  cases hc
  cases hp
  rfl

theorem RationalNestedResourceSystem.eq_of_data (i j : RationalNestedResourceSystem)
    (hM : i.M = j.M) (hL : i.long = j.long) (hS : i.short = j.short) (hI : i.initial = j.initial) : i = j := by
  cases i
  cases j
  cases hM
  cases hL
  cases hS
  cases hI
  rfl

end Blotto
