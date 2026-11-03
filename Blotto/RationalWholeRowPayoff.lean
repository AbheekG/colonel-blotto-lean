import Blotto.RationalSingleFieldLoss

/-! Exact rational payoff evaluation for labelled whole-allocation laws.
The half share at every tie, including zero, agrees with the canonical game.
The finite sums expose their actual labels; no efficient enumeration claim is
made for an implicitly represented exponentially large label set. -/

namespace Blotto
open scoped BigOperators

namespace RationalFieldSelector

def rationalPayoff {m : ℕ} (v : RationalFieldSelector m)
    (bid opponent : Fin m → ℚ) : ℚ :=
  ∑ j, v.weight j * SparseMW.rationalShare (bid j) (opponent j)

theorem rationalPayoff_cast {m : ℕ} (v : RationalFieldSelector m)
    (bid opponent : Fin m → ℚ) :
    (v.rationalPayoff bid opponent : ℝ) =
      payoff v.values (fun j => (bid j : ℝ)) (fun j => (opponent j : ℝ)) := by
  unfold rationalPayoff payoff
  simp only [Rat.cast_sum, Rat.cast_mul, SparseMW.rationalShare_real]
  rfl

theorem rationalPayoff_nonnegative {m : ℕ} (v : RationalFieldSelector m)
    (bid opponent : Fin m → ℚ) : 0 ≤ v.rationalPayoff bid opponent :=
  Finset.sum_nonneg fun j _ => mul_nonneg (v.positive j).le
    (SparseMW.rationalShare_unit _ _).1

theorem rationalPayoff_le_one {m : ℕ} (v : RationalFieldSelector m)
    (bid opponent : Fin m → ℚ) : v.rationalPayoff bid opponent ≤ 1 := by
  calc
    _ ≤ ∑ j, v.weight j := Finset.sum_le_sum fun j _ =>
      mul_le_of_le_one_right (v.positive j).le (SparseMW.rationalShare_unit _ _).2
    _ = 1 := v.sum_one

theorem rationalPayoff_constant_sum {m : ℕ} (v : RationalFieldSelector m)
    (bid opponent : Fin m → ℚ) :
    v.rationalPayoff bid opponent + v.rationalPayoff opponent bid = 1 := by
  unfold rationalPayoff
  rw [← Finset.sum_add_distrib]
  simp_rw [← mul_add, SparseMW.rationalShare_constant_sum, mul_one]
  exact v.sum_one

end RationalFieldSelector

namespace RationalWholeRowLaw

def rationalPurePayoff {r m : ℕ} (law : RationalWholeRowLaw r m)
    (values : RationalFieldSelector m) (bid : Fin m → ℚ) : ℚ :=
  ∑ i, law.weight i * values.rationalPayoff bid (law.row i)

theorem rationalPurePayoff_cast {r m : ℕ} (law : RationalWholeRowLaw r m)
    (values : RationalFieldSelector m) (bid : Fin m → ℚ) :
    (law.rationalPurePayoff values bid : ℝ) =
      purePayoff values.values (fun j => (bid j : ℝ)) law.law := by
  rw [law.purePayoff_eq_sum]
  unfold rationalPurePayoff
  simp only [Rat.cast_sum, Rat.cast_mul, RationalFieldSelector.rationalPayoff_cast]
  rfl

theorem rationalPurePayoff_nonnegative {r m : ℕ} (law : RationalWholeRowLaw r m)
    (values : RationalFieldSelector m) (bid : Fin m → ℚ) :
    0 ≤ law.rationalPurePayoff values bid :=
  Finset.sum_nonneg fun i _ => mul_nonneg (law.nonnegative i)
    (values.rationalPayoff_nonnegative _ _)

theorem rationalPurePayoff_le_one {r m : ℕ} (law : RationalWholeRowLaw r m)
    (values : RationalFieldSelector m) (bid : Fin m → ℚ) :
    law.rationalPurePayoff values bid ≤ 1 := by
  calc
    _ ≤ ∑ i, law.weight i := Finset.sum_le_sum fun i _ =>
      mul_le_of_le_one_right (law.nonnegative i) (values.rationalPayoff_le_one _ _)
    _ = 1 := law.sum_one

end RationalWholeRowLaw
end Blotto
