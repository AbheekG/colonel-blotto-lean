import Blotto.CoordinatePermutation

/-! Permute uniform group coordinates while leaving the mixture coordinate
fixed at the last index. -/

namespace Blotto
open MeasureTheory Set

noncomputable def permutationWithLast {m : ℕ} (π : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr π (Equiv.refl (Fin 1)))).trans finSumFinEquiv

theorem permutationWithLast_castSucc {m : ℕ} (π : Equiv.Perm (Fin m)) (j : Fin m) :
    permutationWithLast π j.castSucc = (π j).castSucc := by
  simp [permutationWithLast]
  rfl

theorem permutationWithLast_last {m : ℕ} (π : Equiv.Perm (Fin m)) :
    permutationWithLast π (Fin.last m) = Fin.last m := by
  simp [permutationWithLast]
  rfl

theorem permutationWithLast_symm_castSucc {m : ℕ} (π : Equiv.Perm (Fin m)) (j : Fin m) :
    (permutationWithLast π).symm j.castSucc = (π.symm j).castSucc := by
  apply (permutationWithLast π).injective
  rw [Equiv.apply_symm_apply, permutationWithLast_castSucc, Equiv.apply_symm_apply]

theorem permutationWithLast_symm_last {m : ℕ} (π : Equiv.Perm (Fin m)) :
    (permutationWithLast π).symm (Fin.last m) = Fin.last m := by
  apply (permutationWithLast π).injective
  rw [Equiv.apply_symm_apply, permutationWithLast_last]

end Blotto
