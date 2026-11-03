import Blotto.RationalFiniteKernel
import Blotto.FairBitBlocks

/-! One flat fair vector has exactly the product expectation of its two
consecutive blocks. The identity is for arbitrary finite real tests and supports
adaptive samplers without pretending block independence is an input assumption. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

theorem fairBitKernel_blocks (R S : ℕ) (f : (Fin R → Bool) → (Fin S → Bool) → ℝ) :
    (fairBitKernel (R + S)).mean (fun bits => f (firstBitBlock R S bits) (secondBitBlock R S bits)) =
      (fairBitKernel R).mean (fun first => (fairBitKernel S).mean (fun second => f first second)) := by
  change (∫ bits, f (firstBitBlock R S bits) (secondBitBlock R S bits)
    ∂(fairBitLaw (R + S) : Measure (Fin (R + S) → Bool))) = _
  rw [fairBitLaw_integral_mean]
  change (1 / (2 : ℝ) ^ (R + S)) *
    (∑ bits, f (firstBitBlock R S bits) (secondBitBlock R S bits)) =
      ∫ first, (∫ second, f first second ∂(fairBitLaw S : Measure (Fin S → Bool)))
        ∂(fairBitLaw R : Measure (Fin R → Bool))
  rw [fairBitLaw_integral_mean]
  simp_rw [fairBitLaw_integral_mean]
  rw [← Equiv.sum_comp (bitBlockEquiv R S)]
  have hBlocks : ∀ pair : (Fin S → Bool) × (Fin R → Bool),
      f (firstBitBlock R S ((bitBlockEquiv R S) pair)) (secondBitBlock R S ((bitBlockEquiv R S) pair)) = f pair.2 pair.1 := by
    intro pair
    have hFirst : firstBitBlock R S ((bitBlockEquiv R S) pair) = pair.2 := by funext i; exact Fin.append_left _ _ i
    have hSecond : secondBitBlock R S ((bitBlockEquiv R S) pair) = pair.1 := by funext i; exact Fin.append_right _ _ i
    rw [hFirst, hSecond]
  simp_rw [hBlocks]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [pow_add]
  field_simp

theorem fairBitKernel_cast (N M : ℕ) (h : N = M) (f : (Fin M → Bool) → ℝ) :
    (fairBitKernel N).mean (fun bits => f (fun j => bits (j.cast h.symm))) = (fairBitKernel M).mean f := by
  subst M
  rfl

end Blotto
