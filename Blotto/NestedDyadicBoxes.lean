import Blotto.NestedDyadicCoupling
import Blotto.DyadicBoxes

/-! Coordinate-box support of all finite nested laws. Nonnegative reflection
can therefore use these approximations, not merely the ideal continuous law. -/

namespace Blotto
open MeasureTheory Set

namespace ThreeSpec

theorem dyadicLaw_inBox (i : ThreeSpec) (K : ℕ) :
    ∀ᵐ x ∂(i.dyadicLaw K : Measure (Allocation 3)), InBox ![i.a, i.d, i.c] x :=
  i.segmentLottery.dyadicLaw_inBox K (fun j => ⟨i.segmentLottery_box.1 j, i.segmentLottery_box.2 j⟩)

end ThreeSpec

namespace NestedInput

theorem firstConditionalDyadicLaw_inBox (i : NestedInput) (htv : i.t ≤ i.v) {s : ℝ}
    (hs : s ∈ Icc 0 i.t) (K : ℕ) :
    ∀ᵐ x ∂(i.firstConditionalDyadicLaw htv s K : Measure (Allocation 3)), InBox ![i.a, i.d, i.c] x := by
  classical
  unfold firstConditionalDyadicLaw
  split_ifs with hp
  · have he := i.firstGeometry_matches htv s hp.1 hp.2
    have hb := (i.firstGeometry htv s hp.1 hp.2).segmentLottery_box
    have ha : ∀ᵐ x ∂((i.firstGeometry htv s hp.1 hp.2).segmentLottery.dyadicLaw K : Measure (Allocation 3)),
        InBox ![i.a, i.d, i.c - s] x := by
      simpa only [he.1, he.2.1, he.2.2.1] using
        (i.firstGeometry htv s hp.1 hp.2).segmentLottery.dyadicLaw_inBox K (fun j => ⟨hb.1 j, hb.2 j⟩)
    simpa only [sub_add_cancel] using shiftedLaw_inBox hs.1 ha
  · rw [dyadicSegmentLaw_eq]
    apply midpointSegmentLaw_inBox
    · intro j
      fin_cases j
      · exact ⟨le_rfl, le_of_lt i.a_pos⟩
      · exact ⟨le_of_lt i.d_pos, le_rfl⟩
      · exact ⟨hs.1, hs.2.trans (le_of_lt i.t_lt)⟩
    · intro j
      fin_cases j
      · exact ⟨le_of_lt i.a_pos, le_rfl⟩
      · exact ⟨le_rfl, le_of_lt i.d_pos⟩
      · exact ⟨hs.1, hs.2.trans (le_of_lt i.t_lt)⟩

theorem firstDyadicApproximation_inBox (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ) :
    ∀ᵐ x ∂(i.firstDyadicApproximation htv K : Measure (Allocation 3)), InBox ![i.a, i.d, i.c] x := by
  apply probabilityMixture_ae
  intro j
  exact i.firstConditionalDyadicLaw_inBox htv
    (i.location_bounds ⟨le_of_lt (midpoint_bounds (pow_pos (by decide : 0 < (2 : ℕ)) K) j).1,
      le_of_lt (midpoint_bounds (pow_pos (by decide : 0 < (2 : ℕ)) K) j).2⟩) K

theorem familyFirstDyadicLaw_inBox (i : NestedInput) (x : ℝ) (hx0 : 0 < x) (hxv : x ≤ i.v) (K : ℕ) :
    ∀ᵐ y ∂(i.familyFirstDyadicLaw x hx0 hxv K : Measure (Allocation 3)), InBox ![i.a, i.d, i.c] y :=
  (i.atLength x hx0 (by linarith [i.lengths.2.2.1])).firstDyadicApproximation_inBox hxv K

theorem secondUniformDyadicLaw_inBox (i : NestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) (K : ℕ) :
    ∀ᵐ x ∂(i.secondUniformDyadicLaw htu hTt K : Measure (Allocation 3)), InBox ![i.a, i.d, i.c] x := by
  have hb := (i.secondUniformInput htu hTt).segmentLottery_box
  have hu : ∀ᵐ x ∂((i.secondUniformInput htu hTt).segmentLottery.dyadicLaw K : Measure (Allocation 3)),
      InBox ![i.a, i.d, i.t - i.mirrorLength] x :=
    (i.secondUniformInput htu hTt).segmentLottery.dyadicLaw_inBox K (fun j => ⟨hb.1 j, hb.2 j⟩)
  have hs : ∀ᵐ x ∂(i.secondUniformDyadicLaw htu hTt K : Measure (Allocation 3)), InBox ![i.a, i.d, i.t] x := by
    simpa only [secondUniformDyadicLaw, sub_add_cancel] using shiftedLaw_inBox (le_of_lt (i.mirrorLength_bounds htu).1) hu
  apply hs.mono
  intro x hx
  apply inBox_mono _ hx
  intro j
  fin_cases j
  · exact le_rfl
  · exact le_rfl
  · exact le_of_lt i.t_lt

theorem secondDyadicLaw_inBox (i : NestedInput) (htu : i.u ≤ i.t) (K : ℕ) :
    ∀ᵐ x ∂(i.secondDyadicLaw htu K : Measure (Allocation 3)), InBox ![i.a, i.d, i.c] x := by
  unfold secondDyadicLaw
  split_ifs with hTt
  · exact binaryLaw_inBox _ _ _ _ (i.familyFirstDyadicLaw_inBox _ _ _ K) (i.secondUniformDyadicLaw_inBox htu hTt K)
  · exact i.familyFirstDyadicLaw_inBox _ _ _ K

theorem thirdDyadicLaw_inBox (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ) :
    ∀ᵐ x ∂(i.thirdDyadicLaw hvt htu K : Measure (Allocation 3)), InBox ![i.a, i.d, i.c] x := by
  have he := i.geometry_matches
  have hr : ∀ᵐ x ∂((i.residualInput hvt htu).dyadicLaw K : Measure (Allocation 3)), InBox ![i.a, i.d, i.c] x := by
    simpa only [NestedResidual.dyadicLaw, residualInput, he.1, he.2.1, he.2.2.1] using
      (i.residualInput hvt htu).segmentLottery.dyadicLaw_inBox K (fun _j =>
        ⟨(i.residualInput hvt htu).vertex_inBox _, (i.residualInput hvt htu).vertex_inBox _⟩)
  unfold thirdDyadicLaw
  split_ifs with hv
  · exact binaryLaw_inBox _ _ _ _ (i.familyFirstDyadicLaw_inBox _ _ _ K) hr
  · exact hr

theorem dyadicLaw_inBox (i : NestedInput) (K : ℕ) :
    ∀ᵐ x ∂(i.dyadicLaw K : Measure (Allocation 3)), InBox ![i.a, i.d, i.c] x := by
  unfold dyadicLaw
  split_ifs with htv htu
  · exact i.firstDyadicApproximation_inBox htv K
  · exact i.secondDyadicLaw_inBox htu K
  · exact i.thirdDyadicLaw_inBox (lt_of_not_ge htv) (lt_of_not_ge htu) K

end NestedInput

namespace NestedSpec

theorem dyadicLaw_inBox (i : NestedSpec) (K : ℕ) :
    ∀ᵐ x ∂(i.dyadicLaw K : Measure (Allocation 3)), InBox ![i.a, i.d, i.c] x := by
  unfold dyadicLaw
  split_ifs with hq0 hq1 had
  · exact (i.longInput hq0).dyadicLaw_inBox K
  · have hb := (i.shortInput hq1).dyadicLaw_inBox K
    apply hb.mono
    intro x hx
    apply inBox_mono _ hx
    intro j
    fin_cases j
    · exact le_rfl
    · exact le_rfl
    · exact le_of_lt i.t_lt
  · have hb := (i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)).dyadicLaw_inBox K
    simpa only [interiorInput, min_eq_left had, max_eq_right had] using hb
  · have hda := le_of_lt (lt_of_not_ge had)
    have hb := swapLaw_inBox ((i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0))
      (lt_of_le_of_ne i.q_le hq1)).dyadicLaw_inBox K)
    simpa only [interiorInput, min_eq_right hda, max_eq_left hda] using hb

end NestedSpec
end Blotto
