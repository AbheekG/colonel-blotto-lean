import Blotto.NestedDyadicBoxes

/-! Every finite nested output path remains inside its coordinate box and
spends the exact budget. The first-case conditional path is also identified
with the maintained real-parameter map at its dyadic argument. -/

namespace Blotto
open MeasureTheory Set

namespace NestedInput

theorem firstConditionalDyadicPoint_eq (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ) (K : ℕ)
    (slot : Fin 9) (bits : Fin K → Bool) :
    i.firstConditionalDyadicPoint htv s K slot bits = i.firstPoint htv s slot (dyadicMidpointSample K bits) := by
  classical
  unfold firstConditionalDyadicPoint firstPoint
  split_ifs <;> rfl

theorem firstDyadicPoint_inBox (i : NestedInput) (htv : i.t ≤ i.v) (K : ℕ)
    (outerBits innerBits : Fin K → Bool) (slot : Fin 9) :
    InBox ![i.a, i.d, i.c] (i.firstDyadicPoint htv K outerBits innerBits slot) := by
  unfold firstDyadicPoint
  rw [i.firstConditionalDyadicPoint_eq]
  exact i.firstPoint_inBox htv (i.dyadicLocation_point_bounds K outerBits)
    ⟨le_of_lt (dyadicMidpointSample_bounds K innerBits).1, le_of_lt (dyadicMidpointSample_bounds K innerBits).2⟩ slot

noncomputable def dyadicPoint (i : NestedInput) (K : ℕ) (useFamily : Bool)
    (outerBits innerBits : Fin K → Bool) (slot : Fin 9) (residualSlot : Fin 3) : Allocation 3 :=
  i.couplingPoint useFamily (dyadicMidpointSample K outerBits) (dyadicMidpointSample K innerBits) slot residualSlot

theorem dyadicPoint_fullBudget (i : NestedInput) (K : ℕ) (useFamily : Bool)
    (outerBits innerBits : Fin K → Bool) (slot : Fin 9) (residualSlot : Fin 3) :
    FullBudget i.M (i.dyadicPoint K useFamily outerBits innerBits slot residualSlot) :=
  i.couplingPoint_fullBudget useFamily
    ⟨le_of_lt (dyadicMidpointSample_bounds K outerBits).1, le_of_lt (dyadicMidpointSample_bounds K outerBits).2⟩
    ⟨le_of_lt (dyadicMidpointSample_bounds K innerBits).1, le_of_lt (dyadicMidpointSample_bounds K innerBits).2⟩ slot residualSlot

theorem dyadicPoint_inBox (i : NestedInput) (K : ℕ) (useFamily : Bool)
    (outerBits innerBits : Fin K → Bool) (slot : Fin 9) (residualSlot : Fin 3) :
    InBox ![i.a, i.d, i.c] (i.dyadicPoint K useFamily outerBits innerBits slot residualSlot) :=
  i.couplingPoint_inBox useFamily
    ⟨le_of_lt (dyadicMidpointSample_bounds K outerBits).1, le_of_lt (dyadicMidpointSample_bounds K outerBits).2⟩
    ⟨le_of_lt (dyadicMidpointSample_bounds K innerBits).1, le_of_lt (dyadicMidpointSample_bounds K innerBits).2⟩ slot residualSlot

end NestedInput

namespace NestedSpec

noncomputable def dyadicPoint (i : NestedSpec) (K : ℕ) (useFamily : Bool)
    (outerBits innerBits : Fin K → Bool) (slot : Fin 9) (residualSlot : Fin 3) : Allocation 3 :=
  i.point useFamily (dyadicMidpointSample K outerBits) (dyadicMidpointSample K innerBits) slot residualSlot

theorem dyadicPoint_fullBudget (i : NestedSpec) (K : ℕ) (useFamily : Bool)
    (outerBits innerBits : Fin K → Bool) (slot : Fin 9) (residualSlot : Fin 3) :
    FullBudget i.M (i.dyadicPoint K useFamily outerBits innerBits slot residualSlot) :=
  i.point_fullBudget useFamily
    ⟨le_of_lt (dyadicMidpointSample_bounds K outerBits).1, le_of_lt (dyadicMidpointSample_bounds K outerBits).2⟩
    ⟨le_of_lt (dyadicMidpointSample_bounds K innerBits).1, le_of_lt (dyadicMidpointSample_bounds K innerBits).2⟩ slot residualSlot

theorem dyadicPoint_inBox (i : NestedSpec) (K : ℕ) (useFamily : Bool)
    (outerBits innerBits : Fin K → Bool) (slot : Fin 9) (residualSlot : Fin 3) :
    InBox ![i.a, i.d, i.c] (i.dyadicPoint K useFamily outerBits innerBits slot residualSlot) :=
  i.point_inBox useFamily
    ⟨le_of_lt (dyadicMidpointSample_bounds K outerBits).1, le_of_lt (dyadicMidpointSample_bounds K outerBits).2⟩
    ⟨le_of_lt (dyadicMidpointSample_bounds K innerBits).1, le_of_lt (dyadicMidpointSample_bounds K innerBits).2⟩ slot residualSlot

end NestedSpec
end Blotto
