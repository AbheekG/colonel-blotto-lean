import Blotto.PlayerSpecificFairAveraging
import Blotto.PlayerSpecificAlgebraicFourSmallDraw

/-! Reserving a larger packet and reading its actual initial subpacket
preserves the exact fair law, including a zero-length packet. -/
namespace Blotto.PlayerSpecificFairPrefix
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem mean (n m : ℕ) (h : n ≤ m) (f : (Fin n → Bool) → ℝ) :
    (∫ bits,f (PlayerSpecificAlgebraicFourSmallDraw.takeBits h bits) ∂(fairBitLaw m : Measure (Fin m → Bool)))=
      ∫ bits,f bits ∂(fairBitLaw n : Measure (Fin n → Bool)) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
  have ht : PlayerSpecificAlgebraicFourSmallDraw.takeBits h=firstBitBlock n k := by
    funext bits j
    rfl
  rw [ht]
  have hi := PlayerSpecificFairBitBlocks.integral_blocks n k (fun first _ => f first)
  simp only [integral_const,probReal_univ,one_smul] at hi
  exact hi

theorem law {α : Type*} [MeasurableSpace α] (n m : ℕ) (h : n ≤ m) (f : (Fin n → Bool) → α) :
    (fairBitLaw m).map (fun bits => f (PlayerSpecificAlgebraicFourSmallDraw.takeBits h bits))=(fairBitLaw n).map f := by
  classical
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro A hA
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((fairBitLaw m).map (fun bits => f (PlayerSpecificAlgebraicFourSmallDraw.takeBits h bits)) : Measure α).real A=
    ((fairBitLaw n).map f : Measure α).real A
  rw [PlayerSpecificFairAveraging.event _ _ A hA,PlayerSpecificFairAveraging.event _ _ A hA]
  exact mean n m h (fun bits => if f bits ∈ A then (1:ℝ) else 0)

end Blotto.PlayerSpecificFairPrefix
