import Blotto.RealThreeGeometryCode

/-! Counted real formula evaluation builds exactly the retained three-variable
segment descriptor. The four stored parameters are shared by every formula. -/

namespace Blotto
open scoped BigOperators

namespace RealThreeGeometryCode
open RationalThreeGeometryCode

noncomputable def compiledLottery (g : ThreeGeometry) : SegmentLottery 3 9 :=
  let env := environment g
  { weight := fun slot => (chosen slot).realValue env
    P := fun slot j => (vertex (threeEdges slot).1 j).realValue env
    Q := fun slot j => (vertex (threeEdges slot).2 j).realValue env
    nonnegative := by
      intro slot
      rw [chosen_value]
      exact g.chosenWeights.vector_nonnegative g.chosenWeights_nonnegative slot
    mass := by
      change (∑ slot, (chosen slot).realValue (environment g)) = 1
      simp only [chosen_value]
      rw [g.chosenWeights.vector_mass]
      exact g.chosenWeights_mass }

theorem compiledLottery_eq (g : ThreeGeometry) : compiledLottery g = g.segmentLottery := by
  apply SegmentLottery.eq_of_fields
  · funext slot
    exact chosen_value g slot
  · funext slot j
    exact vertex_value g _ j
  · funext slot j
    exact vertex_value g _ j

noncomputable def descriptorWork (g : ThreeGeometry) : ℕ :=
  (∑ slot : Fin 9, ((chosen slot).runReal (environment g)).2) +
    (∑ slot : Fin 9, ∑ j : Fin 3, ((vertex (threeEdges slot).1 j).runReal (environment g)).2) +
    (∑ slot : Fin 9, ∑ j : Fin 3, ((vertex (threeEdges slot).2 j).runReal (environment g)).2)

theorem descriptorWork_bound (g : ThreeGeometry) : descriptorWork g ≤ 2736 := by
  have hw : (∑ slot : Fin 9, ((chosen slot).runReal (environment g)).2) ≤ 9 * 256 := by
    calc
      _ ≤ ∑ _slot : Fin 9, 256 := Finset.sum_le_sum (fun slot _ => chosen_operations g slot)
      _ = _ := by simp
  have hP : (∑ slot : Fin 9, ∑ j : Fin 3, ((vertex (threeEdges slot).1 j).runReal (environment g)).2) ≤ 9 * (3 * 8) := by
    calc
      _ ≤ ∑ _slot : Fin 9, ∑ _j : Fin 3, 8 :=
        Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => vertex_operations g _ j))
      _ = _ := by simp
  have hQ : (∑ slot : Fin 9, ∑ j : Fin 3, ((vertex (threeEdges slot).2 j).runReal (environment g)).2) ≤ 9 * (3 * 8) := by
    calc
      _ ≤ ∑ _slot : Fin 9, ∑ _j : Fin 3, 8 :=
        Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => vertex_operations g _ j))
      _ = _ := by simp
  unfold descriptorWork
  omega

end RealThreeGeometryCode
end Blotto
