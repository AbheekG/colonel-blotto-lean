import Blotto.PlayerSpecificAlgebraicNestedSpecProfile

/-! Closed-weight and swapped nested reference endpoints preserve the
original coordinate order, caps and full budget on every stored slot. -/
namespace Blotto.PlayerSpecificAlgebraicNestedSpecProperties
open PlayerSpecificAlgebraicNestedSpecProfile
set_option autoImplicit false

theorem interior_budget (i : NestedSpec) (hq0 : 0 < i.q) (hq1 : i.q < 1) (K : ℕ) (outer : Fin K → Bool) :
    ∀ slot,FullBudget i.M ((interiorReference i hq0 hq1 K outer).P slot) ∧
      FullBudget i.M ((interiorReference i hq0 hq1 K outer).Q slot) := by
  intro slot
  have h := PlayerSpecificAlgebraicNestedInteriorProfile.budget (i.interiorInput hq0 hq1) K outer slot
  unfold interiorReference
  split
  · exact h
  · exact ⟨swapFirst_fullBudget h.1,swapFirst_fullBudget h.2⟩

theorem interior_box (i : NestedSpec) (hq0 : 0 < i.q) (hq1 : i.q < 1) (K : ℕ) (outer : Fin K → Bool) :
    ∀ slot,InBox ![i.a,i.d,i.c] ((interiorReference i hq0 hq1 K outer).P slot) ∧
      InBox ![i.a,i.d,i.c] ((interiorReference i hq0 hq1 K outer).Q slot) := by
  intro slot
  have h := PlayerSpecificAlgebraicNestedInteriorProfile.box (i.interiorInput hq0 hq1) K outer slot
  by_cases had : i.a ≤ i.d
  · rw [interiorReference,ite_eq_left had]
    simpa only [NestedSpec.interiorInput,min_eq_left had,max_eq_right had] using h
  · rw [interiorReference,ite_eq_right had]
    have hda := (lt_of_not_ge had).le
    have hp := PlayerSpecificAlgebraicDescriptorSwap.box h.1
    have hq := PlayerSpecificAlgebraicDescriptorSwap.box h.2
    simpa only [NestedSpec.interiorInput,min_eq_right hda,max_eq_left hda,
      SegmentLottery.mapped,AffineAllocation.swapFirst] using And.intro hp hq

theorem budget (i : NestedSpec) (K : ℕ) (outer : Fin K → Bool) :
    ∀ slot,FullBudget i.M ((reference i K outer).P slot) ∧ FullBudget i.M ((reference i K outer).Q slot) := by
  unfold reference
  split
  · apply PlayerSpecificSegmentAssemblyProperties.pad_property _ 9 0 (FullBudget i.M)
    intro slot
    exact ⟨(NestedSpec.longInput i _).segmentLottery_endpoints.1 slot,(NestedSpec.longInput i _).segmentLottery_endpoints.2 slot⟩
  · split
    · apply PlayerSpecificSegmentAssemblyProperties.pad_property _ 9 0 (FullBudget i.M)
      intro slot
      exact ⟨(NestedSpec.shortInput i _).segmentLottery_endpoints.1 slot,(NestedSpec.shortInput i _).segmentLottery_endpoints.2 slot⟩
    · exact interior_budget i _ _ K outer

theorem box (i : NestedSpec) (K : ℕ) (outer : Fin K → Bool) :
    ∀ slot,InBox ![i.a,i.d,i.c] ((reference i K outer).P slot) ∧ InBox ![i.a,i.d,i.c] ((reference i K outer).Q slot) := by
  unfold reference
  split
  · apply PlayerSpecificSegmentAssemblyProperties.pad_property _ 9 0 (InBox ![i.a,i.d,i.c])
    intro slot
    exact ⟨(NestedSpec.longInput i _).segmentLottery_box.1 slot,(NestedSpec.longInput i _).segmentLottery_box.2 slot⟩
  · split
    · apply PlayerSpecificSegmentAssemblyProperties.pad_property _ 9 0 (InBox ![i.a,i.d,i.c])
      intro slot
      have hq : i.q=1 := by assumption
      have h := (NestedSpec.shortInput i hq).segmentLottery_box
      have caps : ∀ j : Fin 3, (![i.a,i.d,i.t] j) ≤ (![i.a,i.d,i.c] j) := by
        intro j
        fin_cases j
        · exact le_rfl
        · exact le_rfl
        · exact i.t_lt.le
      exact ⟨inBox_mono caps (h.1 slot),inBox_mono caps (h.2 slot)⟩
    · exact interior_box i _ _ K outer

end Blotto.PlayerSpecificAlgebraicNestedSpecProperties
