import Blotto.SortTriple
import Blotto.PermuteWithLast

/-! Native three-comparison sorting and a mixture-coordinate-preserving
permutation. Equal lengths use the same non-strict branch as the real model. -/

namespace Blotto

def rationalComparePermutation (L : Fin 3 → ℚ) (i j : Fin 3) : Equiv.Perm (Fin 3) :=
  if L i ≤ L j then Equiv.refl _ else Equiv.swap i j

def rationalSortTriplePermutation (L : Fin 3 → ℚ) : Equiv.Perm (Fin 3) :=
  let p := rationalComparePermutation L 0 1
  let M := fun j => L (p j)
  let q := rationalComparePermutation M 1 2
  let N := fun j => M (q j)
  let r := rationalComparePermutation N 0 1
  (r.trans q).trans p

def rationalSortedTriple (L : Fin 3 → ℚ) : Fin 3 → ℚ := fun j => L (rationalSortTriplePermutation L j)

def rationalPermutationWithLast {m : ℕ} (π : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr π (Equiv.refl (Fin 1)))).trans finSumFinEquiv

theorem rationalComparePermutation_real (L : Fin 3 → ℚ) (i j : Fin 3) :
    rationalComparePermutation L i j = comparePermutation (fun j => (L j : ℝ)) i j := by
  have he : L i ≤ L j ↔ (L i : ℝ) ≤ (L j : ℝ) := by norm_cast
  unfold rationalComparePermutation comparePermutation
  by_cases h : L i ≤ L j
  · rw [ite_eq_left h, ite_eq_left (he.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h (he.mpr hh))]

theorem rationalSortTriplePermutation_real (L : Fin 3 → ℚ) :
    rationalSortTriplePermutation L = sortTriplePermutation (fun j => (L j : ℝ)) := by
  unfold rationalSortTriplePermutation sortTriplePermutation
  simp only [rationalComparePermutation_real]
  rfl

theorem rationalSortedTriple_real (L : Fin 3 → ℚ) (j : Fin 3) :
    (rationalSortedTriple L j : ℝ) = sortedTriple (fun j => (L j : ℝ)) j := by
  unfold rationalSortedTriple sortedTriple permuteAllocation
  rw [rationalSortTriplePermutation_real]

theorem rationalSortedTriple_ordered (L : Fin 3 → ℚ) :
    rationalSortedTriple L 0 ≤ rationalSortedTriple L 1 ∧ rationalSortedTriple L 1 ≤ rationalSortedTriple L 2 := by
  have h := sortedTriple_ordered (fun j => (L j : ℝ))
  rw [← rationalSortedTriple_real L 0, ← rationalSortedTriple_real L 1, ← rationalSortedTriple_real L 2] at h
  exact_mod_cast h

theorem rationalPermutationWithLast_real {m : ℕ} (π : Equiv.Perm (Fin m)) :
    rationalPermutationWithLast π = permutationWithLast π := rfl

end Blotto
