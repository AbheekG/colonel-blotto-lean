import Blotto.PlayerSpecificSegmentDyadicAssembly
import Blotto.PlayerSpecificAlgebraicNestedFirstProfile
import Blotto.PlayerSpecificSegmentProfileLaw
import Blotto.NestedDyadicCoupling

/-! The first conditional descriptor, including its zero corner, has
exactly the previously checked finite-midpoint law. Its fresh outer
average is the paper's two-scalar midpoint approximation. -/
namespace Blotto.PlayerSpecificNestedFirstDyadicReference
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem conditional (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ) (hs : 0 ≤ s ∧ s ≤ i.t) (K : ℕ) :
    (PlayerSpecificAlgebraicNestedFirstTable.reference i htv s hs).dyadicLaw K=i.firstConditionalDyadicLaw htv s K := by
  classical
  by_cases hp : 0 < i.conditionalProbability s
  · have hin : s ∈ i.positiveParameters := ⟨hs,hp⟩
    rw [PlayerSpecificAlgebraicNestedFirstTable.reference,dite_eq_left hp,
      NestedInput.firstConditionalDyadicLaw,dite_eq_left hin]
    apply ProbabilityMeasure.toMeasure_injective
    change (((i.firstGeometry htv s hs hp).segmentLottery.mapped (AffineAllocation.shiftThird s)).dyadicLaw K : Measure (Allocation 3))=_
    rw [PlayerSpecificSegmentDyadicAssembly.mapped]
    rfl
  · have hin : s ∉ i.positiveParameters := fun h => hp h.2
    rw [PlayerSpecificAlgebraicNestedFirstTable.reference,dite_eq_right hp,
      NestedInput.firstConditionalDyadicLaw,dite_eq_right hin]
    apply ProbabilityMeasure.toMeasure_injective
    simp [SegmentLottery.dyadicLaw,probabilityMixture,mixtureMeasure,Measure.sum_fintype,Fin.sum_univ_succ]

theorem first (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) :
    PlayerSpecificSegmentProfileLaw.reference K (PlayerSpecificAlgebraicNestedFirstProfile.reference i htv K)=
      i.firstDyadicApproximation htv K := by
  unfold PlayerSpecificSegmentProfileLaw.reference
  rw [averaged_fairBit_finite]
  unfold NestedInput.firstDyadicApproximation
  congr 1
  funext j
  rw [PlayerSpecificAlgebraicNestedFirstProfile.reference,PlayerSpecificSegmentDyadicAssembly.pad,conditional]
  have hm : (dyadicMidpointSample K ((bitIndexEquiv K).symm j) : ℝ)=midpoint j := by
    rw [dyadicMidpointSample_real]
    congr 1
    exact (bitIndexEquiv K).apply_symm_apply j
  rw [hm]

theorem family (i : NestedInput) (short : ℝ) (hshort : 0 < short) (hxv : short ≤ i.v) (K : ℕ) :
    PlayerSpecificSegmentProfileLaw.reference K (PlayerSpecificAlgebraicNestedFamilyReference.reference i short hshort hxv K)=
      i.familyFirstDyadicLaw short hshort hxv K := by
  unfold PlayerSpecificSegmentProfileLaw.reference
  rw [averaged_fairBit_finite]
  unfold NestedInput.familyFirstDyadicLaw NestedInput.firstDyadicApproximation
  congr 1
  funext j
  let f := i.atLength short hshort (by linarith [i.lengths.2.2.1])
  have htv : f.t ≤ f.v := hxv
  change (PlayerSpecificAlgebraicNestedFirstTable.reference f htv
    (f.location (dyadicMidpointSample K ((bitIndexEquiv K).symm j))) _).dyadicLaw K=
      f.firstConditionalDyadicLaw htv (f.location (midpoint j)) K
  rw [conditional f htv]
  have hm : (dyadicMidpointSample K ((bitIndexEquiv K).symm j) : ℝ)=midpoint j := by
    rw [dyadicMidpointSample_real]
    congr 1
    exact (bitIndexEquiv K).apply_symm_apply j
  rw [hm]

end Blotto.PlayerSpecificNestedFirstDyadicReference
