import Blotto.GeneralPaperBasisGridInputs

/-! All stored stage coordinates have the paper common denominators.
The original fixed grid, rather than any temporary ray point, supplies
the tail. Determinants of either sign are allowed.
-/
namespace Blotto.GeneralPaperBasisStageLattice
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisPrefixSum
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem point {j d : ℕ} (N : ℕ) (hN : 0<N) (betaN D : ℤ) (hD : D≠0) (A : IntMatrix j)
    (rows : Rows j d) (initial : Vector d) (hj : j≤d) (k : Fin d) :
    OnRationalLattice (N*D.natAbs) ((GeneralPaperBasisFreshPoint.run N betaN D A rows initial).point.read k) := by
  by_cases hk : k.val<j
  · let i : Fin j := ⟨k.val,hk⟩
    have he : embed hj i=k := Fin.ext rfl
    rw [←he,GeneralPaperBasisFreshPoint.first_read N betaN D A rows initial hj i,
      ←GeneralPaperBasisRationalSolve.read]
    exact GeneralPaperBasisRationalSolve.lattice N hN D hD A _ i
  · rw [GeneralPaperBasisFreshPoint.later_read N betaN D A rows initial k (by omega)]
    have hn : (N:ℤ)≠0 := by exact_mod_cast hN.ne'
    have hh := FinitePolytopeRationalWitness.denominator_divInt (numerator := initial.read k)
      (denominator := (N:ℤ)) hn
    have hl : OnRationalLattice N ((initial.read k:ℚ)/(N:ℚ)) := by simpa [OnRationalLattice] using hh
    exact hl.enlarge (Nat.dvd_mul_right N D.natAbs)

theorem direction {j d : ℕ} (D : ℤ) (hD : D≠0) (A : IntMatrix j) (rows : Rows j d)
    (next : Fin d) (hNext : next.val=j) (hj : j≤d) (k : Fin d) :
    OnRationalLattice D.natAbs ((GeneralPaperBasisDirection.run D A rows next).velocity.read k) := by
  by_cases hk : k.val<j
  · let i : Fin j := ⟨k.val,hk⟩
    have he : embed hj i=k := Fin.ext rfl
    rw [←he,GeneralPaperBasisDirection.first_read D A rows next hj i]
    have hh := GeneralPaperBasisRationalSolve.lattice 1 (by decide) D hD A (GeneralPaperBasisDirection.columnRun rows next).1 i
    have hl : OnRationalLattice D.natAbs
        ((GeneralPaperBasisRationalSolve.run 1 D A (GeneralPaperBasisDirection.columnRun rows next).1).values.read i) := by
      simpa only [Nat.one_mul] using hh
    simpa only [zero_sub] using (OnRationalLattice.zero D.natAbs).sub hl
  · by_cases he : k.val=j
    · have heq : k=next := Fin.ext (he.trans hNext.symm)
      rw [heq,GeneralPaperBasisDirection.next_read D A rows next hNext]
      exact OnRationalLattice.intCast D.natAbs 1
    · rw [GeneralPaperBasisDirection.later_read D A rows next k (by omega)]
      exact OnRationalLattice.zero D.natAbs

end Blotto.GeneralPaperBasisStageLattice
