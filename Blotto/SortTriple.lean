import Blotto.CoordinatePermutation

/-! Three comparisons sort three group lengths while retaining an explicit
permutation. Equal lengths are handled by the non-strict comparison branch. -/

namespace Blotto
open MeasureTheory Set

noncomputable def comparePermutation (L : Allocation 3) (i j : Fin 3) : Equiv.Perm (Fin 3) :=
  if L i ≤ L j then Equiv.refl _ else Equiv.swap i j

noncomputable def sortTriplePermutation (L : Allocation 3) : Equiv.Perm (Fin 3) :=
  let p := comparePermutation L 0 1
  let M := permuteAllocation p L
  let q := comparePermutation M 1 2
  let N := permuteAllocation q M
  let r := comparePermutation N 0 1
  (r.trans q).trans p

noncomputable def sortedTriple (L : Allocation 3) : Allocation 3 :=
  permuteAllocation (sortTriplePermutation L) L

theorem sortedTriple_ordered (L : Allocation 3) : sortedTriple L 0 ≤ sortedTriple L 1 ∧ sortedTriple L 1 ≤ sortedTriple L 2 := by
  unfold sortedTriple sortTriplePermutation comparePermutation permuteAllocation
  simp only [Equiv.trans_apply]
  split_ifs
  all_goals simp_all [Equiv.swap_apply_def]
  all_goals try constructor
  all_goals linarith

theorem sortedTriple_pos (L : Allocation 3) (h : ∀ i, 0 < L i) (j : Fin 3) : 0 < sortedTriple L j :=
  h ((sortTriplePermutation L) j)

theorem sortedTriple_bound (L : Allocation 3) {B : ℝ} (h : ∀ i, L i ≤ B) (j : Fin 3) : sortedTriple L j ≤ B :=
  h ((sortTriplePermutation L) j)

end Blotto
