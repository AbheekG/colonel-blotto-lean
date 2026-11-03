import Blotto.PlayerSpecificAlgebraicResidualTable

/-! All residual reference slots satisfy the original nested budget and
box. This includes zero-weight slots and the v=0 boundary. -/
namespace Blotto.PlayerSpecificAlgebraicResidualReference
set_option autoImplicit false

theorem endpoints_budget (i : NestedInput) (hvt : i.v< i.t) (htu : i.t< i.u) :
    (∀ slot,FullBudget i.M ((i.residualInput hvt htu).segmentLottery.P slot)) ∧
      (∀ slot,FullBudget i.M ((i.residualInput hvt htu).segmentLottery.Q slot)) := by
  constructor
  · intro slot
    have h:=(i.residualInput hvt htu).vertex_fullBudget (NestedResidual.edges slot).1
    change FullBudget i.geometry.budget _ at h
    rw [i.geometry_matches.2.2.2] at h
    exact h
  · intro slot
    have h:=(i.residualInput hvt htu).vertex_fullBudget (NestedResidual.edges slot).2
    change FullBudget i.geometry.budget _ at h
    rw [i.geometry_matches.2.2.2] at h
    exact h

theorem endpoints_box (i : NestedInput) (hvt : i.v< i.t) (htu : i.t< i.u) :
    (∀ slot,InBox ![i.a,i.d,i.c] ((i.residualInput hvt htu).segmentLottery.P slot)) ∧
      (∀ slot,InBox ![i.a,i.d,i.c] ((i.residualInput hvt htu).segmentLottery.Q slot)) := by
  have hm:=i.geometry_matches
  constructor
  · intro slot
    have h:=(i.residualInput hvt htu).vertex_inBox (NestedResidual.edges slot).1
    change InBox ![i.geometry.a,i.geometry.d,i.geometry.c] _ at h
    rw [hm.1,hm.2.1,hm.2.2.1] at h
    exact h
  · intro slot
    have h:=(i.residualInput hvt htu).vertex_inBox (NestedResidual.edges slot).2
    change InBox ![i.geometry.a,i.geometry.d,i.geometry.c] _ at h
    rw [hm.1,hm.2.1,hm.2.2.1] at h
    exact h

end Blotto.PlayerSpecificAlgebraicResidualReference
