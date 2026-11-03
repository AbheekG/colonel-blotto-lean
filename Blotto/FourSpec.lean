import Blotto.FourGluingDescriptor
import Blotto.SortTriple
import Blotto.PermuteWithLast

/-! Explicit four-variable laws for unsorted group lengths. Sorting uses the
three-comparison network and the mixture coordinate remains last. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators

structure FourSpec where
  B : ℝ
  length : Allocation 3
  ell : ℝ
  p : ℝ
  length_pos : ∀ j, 0 < length j
  length_le : ∀ j, length j ≤ B
  ell_pos : 0 < ell
  ell_le : ell ≤ B
  p_pos : 0 < p
  p_lt : p < 1
  balance : (∑ j, length j) + p * ell = 2 * B

namespace FourSpec

noncomputable def input (i : FourSpec) : FourInput where
  B := i.B
  u := sortedTriple i.length 0
  v := sortedTriple i.length 1
  w := sortedTriple i.length 2
  ell := i.ell
  p := i.p
  u_pos := sortedTriple_pos i.length i.length_pos 0
  uv := (sortedTriple_ordered i.length).1
  vw := (sortedTriple_ordered i.length).2
  ell_pos := i.ell_pos
  p_pos := i.p_pos
  p_lt := i.p_lt
  w_le := sortedTriple_bound i.length i.length_le 2
  ell_le := i.ell_le
  balance := by
    have he := Equiv.sum_comp (sortTriplePermutation i.length) i.length
    change (∑ j, sortedTriple i.length j) = ∑ j, i.length j at he
    have hb := i.balance
    simp [Fin.sum_univ_succ] at he hb
    linarith

noncomputable def law (i : FourSpec) : Mixed 4 :=
  permuteLaw (permutationWithLast (sortTriplePermutation i.length)).symm i.input.law

theorem law_contract (i : FourSpec) :
    (∀ᵐ x ∂(i.law : Measure (Allocation 4)), FullBudget i.B x) ∧
      (∀ j : Fin 3, (marginal i.law j.castSucc : Measure ℝ) = uniformLaw (i.length j)) ∧
      (marginal i.law 3 : Measure ℝ) = zeroUniformLaw i.ell i.p := by
  have hc := i.input.coupling_contract
  have hm : ∀ j : Fin 3, (marginal i.input.law j.castSucc : Measure ℝ) = uniformLaw (sortedTriple i.length j) := by
    intro j
    fin_cases j
    · exact hc.2.1
    · exact hc.2.2.1
    · exact hc.2.2.2.1
  refine ⟨permuteLaw_fullBudget _ hc.1, ?_, ?_⟩
  · intro j
    rw [law, permuteLaw_marginal, permutationWithLast_symm_castSucc, hm]
    change uniformLaw (i.length ((sortTriplePermutation i.length) ((sortTriplePermutation i.length).symm j))) = _
    rw [Equiv.apply_symm_apply]
  · change (marginal i.law (Fin.last 3) : Measure ℝ) = _
    rw [law, permuteLaw_marginal, permutationWithLast_symm_last]
    exact hc.2.2.2.2

noncomputable def point (i : FourSpec) (useUniform : Bool) (choice : ℕ → Bool) (useFamily : Bool)
    (r t : ℝ) (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) : Allocation 4 :=
  permuteAllocation (permutationWithLast (sortTriplePermutation i.length)).symm
    (i.input.point useUniform choice useFamily r t index edge residualEdge)

theorem point_fullBudget (i : FourSpec) (useUniform : Bool) (choice : ℕ → Bool) (useFamily : Bool)
    {r t : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (index : Fin 81) (edge : Fin 9) (residualEdge : Fin 3) :
    FullBudget i.B (i.point useUniform choice useFamily r t index edge residualEdge) :=
  permuteAllocation_fullBudget _ (i.input.point_fullBudget useUniform choice useFamily hr ht index edge residualEdge)

end FourSpec
end Blotto
