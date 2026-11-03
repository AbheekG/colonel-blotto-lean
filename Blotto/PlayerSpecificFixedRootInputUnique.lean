import Blotto.PlayerSpecificAcceptedInitialLaw

/-! For fixed value rows and gamma, the first mean equation determines
the scale. Accepted inputs with the same data and selected root therefore
give the identical exact whole-allocation coupling. -/
namespace Blotto.PlayerSpecificFixedRootInputUnique
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem scale_numerator {N : ℕ} (a : PlayerSpecificInput N) :
    (∑ j,PlayerSpecificMarginals.probA (a.valuesA.weight j) (a.valuesB.weight j) a.gamma*
      min (a.valuesA.weight j) (a.gamma*a.valuesB.weight j))=2*a.scale := by
  have h := a.meanA
  simp only [PlayerSpecificMarginals.length,←mul_div_assoc,←Finset.sum_div] at h
  exact (div_eq_iff a.scale_pos.ne').mp h

theorem scale_unique {N : ℕ} (a b : PlayerSpecificInput N) (hA : a.valuesA=b.valuesA) (hB : a.valuesB=b.valuesB)
    (hg : a.gamma=b.gamma) : a.scale=b.scale := by
  have ha := scale_numerator a
  have hb := scale_numerator b
  rw [hA,hB,hg] at ha
  linarith only [ha,hb]

theorem ext_data {N : ℕ} (a b : PlayerSpecificInput N) (hA : a.valuesA=b.valuesA) (hB : a.valuesB=b.valuesB)
    (hbudget : a.budget=b.budget) (hg : a.gamma=b.gamma) (hs : a.scale=b.scale) : a=b := by
  cases a
  cases b
  simp_all

theorem eq_of_values_root {N : ℕ} (a b : PlayerSpecificInput N) (hA : a.valuesA=b.valuesA) (hB : a.valuesB=b.valuesB)
    (hbudget : a.budget=b.budget) (hg : a.gamma=b.gamma) : a=b :=
  ext_data a b hA hB hbudget hg (scale_unique a b hA hB hg)

end Blotto.PlayerSpecificFixedRootInputUnique
