import Blotto.PlayerSpecificNestedRemainingDyadicReference
import Blotto.PlayerSpecificAlgebraicNestedSpecProfile
import Blotto.AveragedBitMaps

/-! The exact-weight reference of the executing nested profile is the
maintained dyadic coupling law in every case, including closed q and swaps. -/
namespace Blotto.PlayerSpecificNestedDyadicReference
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem interior (i : NestedInput) (K : ℕ) :
    PlayerSpecificSegmentProfileLaw.reference K (PlayerSpecificAlgebraicNestedInteriorProfile.reference i K)=i.dyadicLaw K := by
  classical
  unfold NestedInput.dyadicLaw
  by_cases htv : i.t ≤ i.v
  · rw [dite_eq_left htv]
    calc
      _ = PlayerSpecificSegmentProfileLaw.reference K (PlayerSpecificAlgebraicNestedFirstProfile.reference i htv K) := by
        apply averaged_fairBit_congr
        intro outer
        rw [PlayerSpecificAlgebraicNestedInteriorProfile.reference,dite_eq_left htv]
      _ = _ := PlayerSpecificNestedFirstDyadicReference.first i htv K
  · rw [dite_eq_right htv]
    by_cases htu : i.u ≤ i.t
    · rw [dite_eq_left htu]
      calc
        _ = PlayerSpecificSegmentProfileLaw.reference K (PlayerSpecificAlgebraicNestedSecondProfile.reference i htu K) := by
          apply averaged_fairBit_congr
          intro outer
          rw [PlayerSpecificAlgebraicNestedInteriorProfile.reference,dite_eq_right htv,dite_eq_left htu]
        _ = _ := PlayerSpecificNestedRemainingDyadicReference.second i htu K
    · rw [dite_eq_right htu]
      calc
        _ = PlayerSpecificSegmentProfileLaw.reference K (PlayerSpecificAlgebraicNestedThirdProfile.reference i (lt_of_not_ge htv) (lt_of_not_ge htu) K) := by
          apply averaged_fairBit_congr
          intro outer
          rw [PlayerSpecificAlgebraicNestedInteriorProfile.reference,dite_eq_right htv,dite_eq_right htu]
        _ = _ := PlayerSpecificNestedRemainingDyadicReference.third i _ _ K

theorem spec (i : NestedSpec) (K : ℕ) :
    PlayerSpecificSegmentProfileLaw.reference K (PlayerSpecificAlgebraicNestedSpecProfile.reference i K)=i.dyadicLaw K := by
  classical
  unfold NestedSpec.dyadicLaw
  by_cases hq0 : i.q=0
  · rw [dite_eq_left hq0]
    calc
      _ = averagedLaw (fairBitLaw K) (fun _ => (i.longInput hq0).dyadicLaw K) (measurable_of_countable _) := by
        apply averaged_fairBit_congr
        intro outer
        rw [PlayerSpecificAlgebraicNestedSpecProfile.reference,dite_eq_left hq0,PlayerSpecificSegmentDyadicAssembly.pad]
        rfl
      _ = _ := averaged_fairBit_constant K _
  · rw [dite_eq_right hq0]
    by_cases hq1 : i.q=1
    · rw [dite_eq_left hq1]
      calc
        _ = averagedLaw (fairBitLaw K) (fun _ => (i.shortInput hq1).dyadicLaw K) (measurable_of_countable _) := by
          apply averaged_fairBit_congr
          intro outer
          rw [PlayerSpecificAlgebraicNestedSpecProfile.reference,dite_eq_right hq0,dite_eq_left hq1,
            PlayerSpecificSegmentDyadicAssembly.pad]
          rfl
        _ = _ := averaged_fairBit_constant K _
    · rw [dite_eq_right hq1]
      let j := i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)
      by_cases had : i.a ≤ i.d
      · simp only [had,ite_true]
        calc
          _ = PlayerSpecificSegmentProfileLaw.reference K (PlayerSpecificAlgebraicNestedInteriorProfile.reference j K) := by
            apply averaged_fairBit_congr
            intro outer
            rw [PlayerSpecificAlgebraicNestedSpecProfile.reference,dite_eq_right hq0,dite_eq_right hq1,
              PlayerSpecificAlgebraicNestedSpecProfile.interiorReference,ite_eq_left had]
          _ = _ := interior j K
      · simp only [had,ite_false]
        calc
          _ = averagedLaw (fairBitLaw K) (fun outer =>
              ((PlayerSpecificAlgebraicNestedInteriorProfile.reference j K outer).dyadicLaw K).map swapFirst)
                (measurable_of_countable _) := by
            apply averaged_fairBit_congr
            intro outer
            rw [PlayerSpecificAlgebraicNestedSpecProfile.reference,dite_eq_right hq0,dite_eq_right hq1,
              PlayerSpecificAlgebraicNestedSpecProfile.interiorReference,ite_eq_right had]
            apply ProbabilityMeasure.toMeasure_injective
            exact PlayerSpecificSegmentDyadicAssembly.mapped _ AffineAllocation.swapFirst K
          _ = _ := by
            rw [averaged_fairBit_map K _ swapFirst measurable_swapFirst]
            change (PlayerSpecificSegmentProfileLaw.reference K (PlayerSpecificAlgebraicNestedInteriorProfile.reference j K)).map swapFirst=_
            rw [interior j K]
            rfl

end Blotto.PlayerSpecificNestedDyadicReference
