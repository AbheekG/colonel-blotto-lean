import Blotto.PlayerSpecificFiniteSamplerLaw
import Blotto.FairBitExpectation

/-! Arbitrary finite fresh blocks have the exact iterated expectation.
This works for adaptive continuations without assuming independent
coordinates within a sampled allocation. -/
namespace Blotto.PlayerSpecificFairBitBlocks
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem integral_blocks (R S : ℕ) (f : (Fin R → Bool) → (Fin S → Bool) → ℝ) :
    (∫ bits,f (firstBitBlock R S bits) (secondBitBlock R S bits)
      ∂(fairBitLaw (R+S) : Measure (Fin (R+S) → Bool)))=
      ∫ first,(∫ second,f first second ∂(fairBitLaw S : Measure (Fin S → Bool)))
        ∂(fairBitLaw R : Measure (Fin R → Bool)) := by
  simp_rw [fairBitLaw_integral_mean]
  rw [← Equiv.sum_comp (bitBlockEquiv R S) (fun bits => f (firstBitBlock R S bits) (secondBitBlock R S bits))]
  have he : ∀ pair : (Fin S → Bool) × (Fin R → Bool),
      f (firstBitBlock R S ((bitBlockEquiv R S) pair)) (secondBitBlock R S ((bitBlockEquiv R S) pair))=f pair.2 pair.1 := by
    intro pair
    change f (firstBitBlock R S (Fin.append pair.2 pair.1)) (secondBitBlock R S (Fin.append pair.2 pair.1))=f pair.2 pair.1
    have hf : firstBitBlock R S (Fin.append pair.2 pair.1)=pair.2 := by
      funext j; exact Fin.append_left _ _ j
    have hs : secondBitBlock R S (Fin.append pair.2 pair.1)=pair.1 := by
      funext j; exact Fin.append_right _ _ j
    rw [hf,hs]
  simp_rw [he]
  rw [Fintype.sum_prod_type,Finset.sum_comm,← Finset.mul_sum,pow_add]
  field_simp

noncomputable def success (H : ℕ) (coin : (Fin H → Bool) → Bool) : ℝ :=
  (fairBitLaw H : Measure (Fin H → Bool)).real {bits | coin bits=true}

theorem indicator_mean (H : ℕ) (coin : (Fin H → Bool) → Bool) :
    (∫ bits,(if coin bits then (1:ℝ) else 0) ∂(fairBitLaw H : Measure (Fin H → Bool)))=success H coin := by
  let A : Set (Fin H → Bool) := {bits | coin bits=true}
  have hA : MeasurableSet A := A.to_countable.measurableSet
  have he : (fun bits => if coin bits then (1:ℝ) else 0)=A.indicator (fun _ => (1:ℝ)) := by
    funext bits
    simp only [A,Set.indicator_apply,Set.mem_ofPred_eq]
  rw [he,integral_indicator_const _ hA,smul_eq_mul,mul_one]
  rfl

theorem bool_mean (H : ℕ) (coin : (Fin H → Bool) → Bool) (upper lower : ℝ) :
    (∫ bits,(if coin bits then upper else lower) ∂(fairBitLaw H : Measure (Fin H → Bool)))=
      success H coin*upper+(1-success H coin)*lower := by
  have he : (fun bits => if coin bits then upper else lower)=
      (fun bits => lower+(upper-lower)*(if coin bits then (1:ℝ) else 0)) := by
    funext bits
    cases coin bits <;> simp
  rw [he,integral_add Integrable.of_finite Integrable.of_finite,integral_const,probReal_univ,one_smul,
    integral_const_mul,indicator_mean]
  ring

theorem binary_continuation (H S : ℕ) (coin : (Fin H → Bool) → Bool)
    (upper lower : (Fin S → Bool) → ℝ) :
    (∫ bits,(if coin (firstBitBlock H S bits) then upper (secondBitBlock H S bits) else lower (secondBitBlock H S bits))
      ∂(fairBitLaw (H+S) : Measure (Fin (H+S) → Bool)))=
      success H coin*(∫ bits,upper bits ∂(fairBitLaw S : Measure (Fin S → Bool)))+
        (1-success H coin)*(∫ bits,lower bits ∂(fairBitLaw S : Measure (Fin S → Bool))) := by
  rw [integral_blocks H S (fun first second => if coin first then upper second else lower second)]
  have he : ∀ first,(∫ second,(if coin first then upper second else lower second) ∂(fairBitLaw S : Measure (Fin S → Bool)))=
      if coin first then (∫ second,upper second ∂(fairBitLaw S : Measure (Fin S → Bool)))
        else (∫ second,lower second ∂(fairBitLaw S : Measure (Fin S → Bool))) := by
    intro first
    cases coin first <;> simp
  simp_rw [he]
  exact bool_mean H coin _ _

end Blotto.PlayerSpecificFairBitBlocks
