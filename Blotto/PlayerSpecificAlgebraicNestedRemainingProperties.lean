import Blotto.PlayerSpecificAlgebraicNestedSecondProfile

/-! Every endpoint of both remaining nested profiles is feasible. The
proofs retain the zero-weight padding used by the executable descriptor. -/
namespace Blotto.PlayerSpecificAlgebraicNestedRemainingProperties
open PlayerSpecificSegmentAssemblyProperties
set_option autoImplicit false

theorem third_property (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ) (outer : Fin K → Bool)
    (P : Allocation 3 → Prop)
    (hf : ∀ (hv : 0 < i.v) slot,P ((PlayerSpecificAlgebraicNestedFamilyReference.reference i i.v hv le_rfl K outer).P slot) ∧
      P ((PlayerSpecificAlgebraicNestedFamilyReference.reference i i.v hv le_rfl K outer).Q slot))
    (hr : ∀ slot,P ((i.residualInput hvt htu).segmentLottery.P slot) ∧ P ((i.residualInput hvt htu).segmentLottery.Q slot)) :
    ∀ slot,P ((PlayerSpecificAlgebraicNestedThirdProfile.reference i hvt htu K outer).P slot) ∧
      P ((PlayerSpecificAlgebraicNestedThirdProfile.reference i hvt htu K outer).Q slot) := by
  have hp := pad_property (i.residualInput hvt htu).segmentLottery 6 0 P hr
  unfold PlayerSpecificAlgebraicNestedThirdProfile.reference
  split
  · exact binary_property _ _ _ _ P (hf _) hp
  · exact pad_property _ 9 0 P hp

theorem second_property (i : NestedInput) (htu : i.u ≤ i.t) (K : ℕ) (outer : Fin K → Bool)
    (P : Allocation 3 → Prop)
    (hf : ∀ slot,P ((PlayerSpecificAlgebraicNestedFamilyReference.reference i i.mirrorLength
      (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K outer).P slot) ∧
      P ((PlayerSpecificAlgebraicNestedFamilyReference.reference i i.mirrorLength
        (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K outer).Q slot))
    (hu : ∀ (hmir : i.mirrorLength < i.t) slot,P ((PlayerSpecificAlgebraicNestedSecondUniform.reference i htu hmir).P slot) ∧
      P ((PlayerSpecificAlgebraicNestedSecondUniform.reference i htu hmir).Q slot)) :
    ∀ slot,P ((PlayerSpecificAlgebraicNestedSecondProfile.reference i htu K outer).P slot) ∧
      P ((PlayerSpecificAlgebraicNestedSecondProfile.reference i htu K outer).Q slot) := by
  unfold PlayerSpecificAlgebraicNestedSecondProfile.reference
  split
  · exact binary_property _ _ _ _ P hf (hu _)
  · exact pad_property _ 9 0 P hf

theorem third_budget (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ) (outer : Fin K → Bool) :
    ∀ slot,FullBudget i.M ((PlayerSpecificAlgebraicNestedThirdProfile.reference i hvt htu K outer).P slot) ∧
      FullBudget i.M ((PlayerSpecificAlgebraicNestedThirdProfile.reference i hvt htu K outer).Q slot) :=
  third_property i hvt htu K outer (FullBudget i.M)
    (fun hv slot => ⟨(PlayerSpecificAlgebraicNestedFamilyReference.endpoints_budget i i.v hv le_rfl K outer).1 slot,
      (PlayerSpecificAlgebraicNestedFamilyReference.endpoints_budget i i.v hv le_rfl K outer).2 slot⟩)
    (fun slot => ⟨(PlayerSpecificAlgebraicResidualReference.endpoints_budget i hvt htu).1 slot,
      (PlayerSpecificAlgebraicResidualReference.endpoints_budget i hvt htu).2 slot⟩)

theorem third_box (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ) (outer : Fin K → Bool) :
    ∀ slot,InBox ![i.a,i.d,i.c] ((PlayerSpecificAlgebraicNestedThirdProfile.reference i hvt htu K outer).P slot) ∧
      InBox ![i.a,i.d,i.c] ((PlayerSpecificAlgebraicNestedThirdProfile.reference i hvt htu K outer).Q slot) :=
  third_property i hvt htu K outer (InBox ![i.a,i.d,i.c])
    (fun hv slot => ⟨(PlayerSpecificAlgebraicNestedFamilyReference.endpoints_box i i.v hv le_rfl K outer).1 slot,
      (PlayerSpecificAlgebraicNestedFamilyReference.endpoints_box i i.v hv le_rfl K outer).2 slot⟩)
    (fun slot => ⟨(PlayerSpecificAlgebraicResidualReference.endpoints_box i hvt htu).1 slot,
      (PlayerSpecificAlgebraicResidualReference.endpoints_box i hvt htu).2 slot⟩)

theorem second_budget (i : NestedInput) (htu : i.u ≤ i.t) (K : ℕ) (outer : Fin K → Bool) :
    ∀ slot,FullBudget i.M ((PlayerSpecificAlgebraicNestedSecondProfile.reference i htu K outer).P slot) ∧
      FullBudget i.M ((PlayerSpecificAlgebraicNestedSecondProfile.reference i htu K outer).Q slot) :=
  second_property i htu K outer (FullBudget i.M)
    (fun slot => ⟨(PlayerSpecificAlgebraicNestedFamilyReference.endpoints_budget i i.mirrorLength
      (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K outer).1 slot,
      (PlayerSpecificAlgebraicNestedFamilyReference.endpoints_budget i i.mirrorLength
        (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K outer).2 slot⟩)
    (fun hmir slot => ⟨(PlayerSpecificAlgebraicNestedSecondReference.endpoints_budget i htu hmir).1 slot,
      (PlayerSpecificAlgebraicNestedSecondReference.endpoints_budget i htu hmir).2 slot⟩)

theorem second_box (i : NestedInput) (htu : i.u ≤ i.t) (K : ℕ) (outer : Fin K → Bool) :
    ∀ slot,InBox ![i.a,i.d,i.c] ((PlayerSpecificAlgebraicNestedSecondProfile.reference i htu K outer).P slot) ∧
      InBox ![i.a,i.d,i.c] ((PlayerSpecificAlgebraicNestedSecondProfile.reference i htu K outer).Q slot) :=
  second_property i htu K outer (InBox ![i.a,i.d,i.c])
    (fun slot => ⟨(PlayerSpecificAlgebraicNestedFamilyReference.endpoints_box i i.mirrorLength
      (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K outer).1 slot,
      (PlayerSpecificAlgebraicNestedFamilyReference.endpoints_box i i.mirrorLength
        (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K outer).2 slot⟩)
    (fun hmir slot => ⟨(PlayerSpecificAlgebraicNestedSecondReference.endpoints_box i htu hmir).1 slot,
      (PlayerSpecificAlgebraicNestedSecondReference.endpoints_box i htu hmir).2 slot⟩)

end Blotto.PlayerSpecificAlgebraicNestedRemainingProperties
