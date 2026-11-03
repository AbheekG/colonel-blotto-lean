import Blotto.RealExpression
import Blotto.RationalNestedResidualCode
import Blotto.NestedDyadicFamilies

/-! Counted real compilation of the residual's complete three-slot descriptor.
All zero weights and endpoints are retained exactly. -/

namespace Blotto.RealNestedResidualCode
open RationalNestedResidualCode
open scoped BigOperators

noncomputable def environment (r : NestedResidual) : FixedArrayTable 5 ℝ :=
  FixedArrayTable.ofFn ![r.g.u, r.g.v, r.g.w, r.g.h, r.t]

theorem weight_value (r : NestedResidual) (slot : Fin 3) :
    (weights slot).realValue (environment r) = r.weight slot := by
  fin_cases slot <;> simp [weights, denominator, G, D, S, U, V, W, H, T, environment,
    FixedArrayTable.read_ofFn, NestedResidual.weight, NestedResidual.K,
    NestedResidual.s, ThreeGeometry.G, ThreeGeometry.d]

theorem vertex_value (r : NestedResidual) (slot j : Fin 3) :
    (vertices slot j).realValue (environment r) = r.vertex slot j := by
  fin_cases slot <;> fin_cases j <;> simp [vertices, A, D, C, S, U, V, W, H, T, environment,
    FixedArrayTable.read_ofFn, NestedResidual.vertex, NestedResidual.s,
    ThreeGeometry.a, ThreeGeometry.d, ThreeGeometry.c]

noncomputable def compiledLottery (r : NestedResidual) : SegmentLottery 3 3 :=
  let env := environment r
  { weight := fun slot => (weights slot).realValue env
    P := fun slot j => (vertices (NestedResidual.edges slot).1 j).realValue env
    Q := fun slot j => (vertices (NestedResidual.edges slot).2 j).realValue env
    nonnegative := by intro slot; rw [weight_value]; exact r.weight_nonnegative slot
    mass := by
      change (∑ slot, (weights slot).realValue (environment r)) = 1
      simp only [weight_value]
      exact r.weight_mass }

theorem compiledLottery_eq (r : NestedResidual) : compiledLottery r = r.segmentLottery := by
  apply SegmentLottery.eq_of_fields
  · funext slot; exact weight_value r slot
  · funext slot j; exact vertex_value r _ j
  · funext slot j; exact vertex_value r _ j

theorem weight_operations (r : NestedResidual) (slot : Fin 3) :
    ((weights slot).runReal (environment r)).2 ≤ 128 :=
  ((weights slot).runReal_operations_le _).trans (weight_operationBound slot)

theorem vertex_operations (r : NestedResidual) (slot j : Fin 3) :
    ((vertices slot j).runReal (environment r)).2 ≤ 16 :=
  ((vertices slot j).runReal_operations_le _).trans (vertex_operationBound slot j)

noncomputable def descriptorWork (r : NestedResidual) : ℕ :=
  (∑ slot : Fin 3, ((weights slot).runReal (environment r)).2) +
    (∑ slot : Fin 3, ∑ j : Fin 3, ((vertices (NestedResidual.edges slot).1 j).runReal (environment r)).2) +
    (∑ slot : Fin 3, ∑ j : Fin 3, ((vertices (NestedResidual.edges slot).2 j).runReal (environment r)).2)

theorem descriptorWork_bound (r : NestedResidual) : descriptorWork r ≤ 672 := by
  have hw : (∑ slot : Fin 3, ((weights slot).runReal (environment r)).2) ≤ 3 * 128 := by
    calc
      _ ≤ ∑ _slot : Fin 3, 128 := Finset.sum_le_sum (fun slot _ => weight_operations r slot)
      _ = _ := by simp
  have hP : (∑ slot : Fin 3, ∑ j : Fin 3, ((vertices (NestedResidual.edges slot).1 j).runReal (environment r)).2) ≤ 3 * (3 * 16) := by
    calc
      _ ≤ ∑ _slot : Fin 3, ∑ _j : Fin 3, 16 :=
        Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => vertex_operations r _ j))
      _ = _ := by simp
  have hQ : (∑ slot : Fin 3, ∑ j : Fin 3, ((vertices (NestedResidual.edges slot).2 j).runReal (environment r)).2) ≤ 3 * (3 * 16) := by
    calc
      _ ≤ ∑ _slot : Fin 3, ∑ _j : Fin 3, 16 :=
        Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => vertex_operations r _ j))
      _ = _ := by simp
  unfold descriptorWork
  omega

end Blotto.RealNestedResidualCode
