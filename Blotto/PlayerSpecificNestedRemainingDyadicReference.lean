import Blotto.PlayerSpecificNestedFirstDyadicReference
import Blotto.PlayerSpecificAlgebraicNestedInteriorProfile
import Blotto.AveragedBitMixtures

/-! Exact finite-midpoint reference identities for the second and third
nested cases, including omitted zero-weight families and residual slots. -/
namespace Blotto.PlayerSpecificNestedRemainingDyadicReference
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem uniform (i : NestedInput) (htu : i.u ≤ i.t) (hmir : i.mirrorLength < i.t) (K : ℕ) :
    (PlayerSpecificAlgebraicNestedSecondUniform.reference i htu hmir).dyadicLaw K=i.secondUniformDyadicLaw htu hmir K := by
  apply ProbabilityMeasure.toMeasure_injective
  exact PlayerSpecificSegmentDyadicAssembly.mapped _ (AffineAllocation.shiftThird i.mirrorLength) K

theorem residual (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ) :
    (PlayerSpecificAlgebraicNestedThirdProfile.residualReference i hvt htu).dyadicLaw K=(i.residualInput hvt htu).dyadicLaw K :=
  PlayerSpecificSegmentDyadicAssembly.pad _ 6 K 0

theorem second (i : NestedInput) (htu : i.u ≤ i.t) (K : ℕ) :
    PlayerSpecificSegmentProfileLaw.reference K (PlayerSpecificAlgebraicNestedSecondProfile.reference i htu K)=
      i.secondDyadicLaw htu K := by
  classical
  unfold PlayerSpecificSegmentProfileLaw.reference NestedInput.secondDyadicLaw
  by_cases hmir : i.mirrorLength < i.t
  · rw [dite_eq_left hmir]
    calc
      _ = averagedLaw (fairBitLaw K) (fun outer => binaryLaw i.secondAlpha
          ⟨(i.secondAlpha_bounds htu).1.le,(i.secondAlpha_bounds htu).2⟩
          ((PlayerSpecificAlgebraicNestedFamilyReference.reference i i.mirrorLength
            (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K outer).dyadicLaw K)
          (i.secondUniformDyadicLaw htu hmir K)) (measurable_of_countable _) := by
        apply averaged_fairBit_congr
        intro outer
        rw [PlayerSpecificAlgebraicNestedSecondProfile.reference,dite_eq_left hmir,
          PlayerSpecificSegmentDyadicAssembly.binary,uniform]
      _ = _ := by
        rw [averaged_fairBit_binary,averaged_fairBit_constant]
        rw [←PlayerSpecificSegmentProfileLaw.reference,PlayerSpecificNestedFirstDyadicReference.family]
  · rw [dite_eq_right hmir]
    calc
      _ = PlayerSpecificSegmentProfileLaw.reference K (PlayerSpecificAlgebraicNestedFamilyReference.reference i i.mirrorLength
          (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K) := by
        apply averaged_fairBit_congr
        intro outer
        rw [PlayerSpecificAlgebraicNestedSecondProfile.reference,dite_eq_right hmir,PlayerSpecificSegmentDyadicAssembly.pad]
      _ = _ := PlayerSpecificNestedFirstDyadicReference.family _ _ _ _ _

theorem third (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ) :
    PlayerSpecificSegmentProfileLaw.reference K (PlayerSpecificAlgebraicNestedThirdProfile.reference i hvt htu K)=
      i.thirdDyadicLaw hvt htu K := by
  classical
  unfold PlayerSpecificSegmentProfileLaw.reference NestedInput.thirdDyadicLaw
  by_cases hv : 0 < i.v
  · rw [dite_eq_left hv]
    calc
      _ = averagedLaw (fairBitLaw K) (fun outer => binaryLaw i.thirdAlpha
          ⟨(i.thirdAlpha_bounds hv hvt).1.le,(i.thirdAlpha_bounds hv hvt).2.le⟩
          ((PlayerSpecificAlgebraicNestedFamilyReference.reference i i.v hv le_rfl K outer).dyadicLaw K)
          ((i.residualInput hvt htu).dyadicLaw K)) (measurable_of_countable _) := by
        apply averaged_fairBit_congr
        intro outer
        rw [PlayerSpecificAlgebraicNestedThirdProfile.reference,dite_eq_left hv,
          PlayerSpecificSegmentDyadicAssembly.binary,residual]
      _ = _ := by
        rw [averaged_fairBit_binary,averaged_fairBit_constant]
        rw [←PlayerSpecificSegmentProfileLaw.reference,PlayerSpecificNestedFirstDyadicReference.family]
  · rw [dite_eq_right hv]
    calc
      _ = averagedLaw (fairBitLaw K) (fun _ => (i.residualInput hvt htu).dyadicLaw K) (measurable_of_countable _) := by
        apply averaged_fairBit_congr
        intro outer
        rw [PlayerSpecificAlgebraicNestedThirdProfile.reference,dite_eq_right hv,
          PlayerSpecificSegmentDyadicAssembly.pad,residual]
      _ = _ := averaged_fairBit_constant K _

end Blotto.PlayerSpecificNestedRemainingDyadicReference
