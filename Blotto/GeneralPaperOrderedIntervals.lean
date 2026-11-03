import Blotto.GeneralPaperRawEpochCDF

/-! Exact interval meaning of prefix differences. These sums are reference
semantics of the full law, not runtime enumeration of its code alphabet.
-/
namespace Blotto.GeneralPaperOrderedIntervals
open scoped BigOperators
open GeneralPaperOrderedVariation
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def mass (p : ℕ → ℝ) (lo hi : ℕ) : ℝ := prefixMass p hi-prefixMass p lo

theorem mass_sum (p : ℕ → ℝ) (lo hi : ℕ) (hOrder : lo≤hi) :
    mass p lo hi=∑ i∈Finset.range (hi-lo), p (lo+i) := by
  have hs := Finset.sum_range_add p lo (hi-lo)
  rw [Nat.add_sub_of_le hOrder] at hs
  unfold mass prefixMass
  linarith

theorem signed_tail_sum (p : ℕ → ℝ) (U a : ℕ) (hA : a≤U) :
    mass p a U-mass p (U+a) (2*U)=∑ i∈Finset.range (U-a), (p (a+i)-p (U+(a+i))) := by
  rw [mass_sum p a U hA,mass_sum p (U+a) (2*U) (by omega)]
  rw [show 2*U-(U+a)=U-a by omega,Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.add_assoc]

end Blotto.GeneralPaperOrderedIntervals
