import Blotto.RealNestedParametersCode

/-! The first conditional geometry is built from four counted real programs.
Its positivity/order proof fields come from exact numerical refinement. -/

namespace Blotto

theorem ThreeGeometry.eq_of_fields (a b : ThreeGeometry) (hu : a.u = b.u) (hv : a.v = b.v)
    (hw : a.w = b.w) (hh : a.h = b.h) : a = b := by
  cases a
  cases b
  cases hu
  cases hv
  cases hw
  cases hh
  rfl

namespace RealNestedParametersCode

noncomputable def firstParameterTable (i : NestedInput) (x : ℝ) : FixedArrayTable 4 ℝ :=
  let env := environment i x
  FixedArrayTable.ofFn fun j => (RationalNestedParametersCode.firstParameters j).realValue env

theorem firstParameterTable_eq (i : NestedInput) (htv : i.t ≤ i.v) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ i.t) (hp : 0 < i.conditionalProbability x) :
    (firstParameterTable i x).read = (RealThreeGeometryCode.environment (i.firstGeometry htv x hx hp)).read := by
  funext j
  rw [firstParameterTable, FixedArrayTable.read_ofFn]
  exact firstParameters_value i htv x hx hp j

noncomputable def firstGeometry (i : NestedInput) (htv : i.t ≤ i.v) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ i.t) (hp : 0 < i.conditionalProbability x) : ThreeGeometry := by
  let g := i.firstGeometry htv x hx hp
  let params := firstParameterTable i x
  have hRead := firstParameterTable_eq i htv x hx hp
  have hu : params.read 0 = g.u := by simpa [RealThreeGeometryCode.environment, FixedArrayTable.read_ofFn, params, g] using congrFun hRead 0
  have hv : params.read 1 = g.v := by simpa [RealThreeGeometryCode.environment, FixedArrayTable.read_ofFn, params, g] using congrFun hRead 1
  have hw : params.read 2 = g.w := by simpa [RealThreeGeometryCode.environment, FixedArrayTable.read_ofFn, params, g] using congrFun hRead 2
  have hh : params.read 3 = g.h := by simpa [RealThreeGeometryCode.environment, FixedArrayTable.read_ofFn, params, g] using congrFun hRead 3
  exact
    { u := params.read 0
      v := params.read 1
      w := params.read 2
      h := params.read 3
      u_pos := by rw [hu]; exact g.u_pos
      v_nonneg := by rw [hv]; exact g.v_nonneg
      w_nonneg := by rw [hw]; exact g.w_nonneg
      h_nonneg := by rw [hh]; exact g.h_nonneg
      ordered := by rw [hu, hv]; exact g.ordered
      a_pos := by rw [hv, hw, hh]; exact g.a_pos
      E_pos := by rw [hw, hh]; exact g.E_pos }

theorem firstGeometry_eq (i : NestedInput) (htv : i.t ≤ i.v) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ i.t) (hp : 0 < i.conditionalProbability x) :
    firstGeometry i htv x hx hp = i.firstGeometry htv x hx hp := by
  apply ThreeGeometry.eq_of_fields
  all_goals change (firstParameterTable i x).read _ = _
  all_goals rw [firstParameterTable_eq i htv x hx hp]
  all_goals rfl

end RealNestedParametersCode
end Blotto
