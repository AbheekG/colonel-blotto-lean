import Blotto.GeneralPaperBasisFreshRHSSize

/-! Fresh point and velocity heights at an arbitrary valid native stage.
The point's unit-box feasibility and fixed N*D lattice give a short bound;
the velocity comes from its actual original-column adjugate product.
-/
namespace Blotto.GeneralPaperBasisStageSize
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisInvariant
open GeneralPaperBasisPrefixSum GeneralPaperProxyParameters
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem int_height (a : ℤ) (A : ℕ) (ha : a.natAbs≤A) : RationalHeight (a:ℚ) (binaryWordWidth A) := by
  have hp : 1<(2:ℕ)^(binaryWordWidth A) := Nat.one_lt_pow (by have hh:=binaryWordWidth_pos A; omega) (by decide)
  exact ⟨by simpa only [Rat.num_intCast] using ha.trans_lt (lt_pow_binaryWordWidth A),
    by simpa only [Rat.den_intCast] using hp⟩

theorem point_height {T m j : ℕ} (k : ℕ) (hm : 0<m) (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K)
    (v : RationalFieldSelector m) (S h N : ℕ) (hN : 0<N) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (hj : j≤m*((prepare m k).K-1)) (state : GeneralPaperBasisState.State j (m*((prepare m k).K-1)))
    (inv : Invariant dict v S h N betaN initialGrid hj state) (a : Fin (m*((prepare m k).K-1))) :
    RationalHeight ((GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point.read a)
      (binaryWordWidth N+binaryWordWidth (prepare m k).H) := by
  have hBox : 0≤(GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point.read a ∧
      (GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point.read a≤1 := by
    obtain ⟨u,rfl⟩ := GeneralPaperBasisCoordinates.index_surjective m (prepare m k).K a
    have hh := ((GeneralPaperAffineConstraintSemantics.feasible_iff dict.label (GeneralPaperStrictScore.score v S) h _ _).mp inv.feasible).1 u
    dsimp only [GeneralPaperBasisFreshPointSound.values] at hh
    exact_mod_cast hh
  have hLat := GeneralPaperBasisStageLattice.point N hN betaN state.determinant inv.nonzero state.adjugate state.rows initialGrid hj a
  have hs := rationalHeight_unit_lattice (Nat.mul_pos hN (Int.natAbs_pos.mpr inv.nonzero)) hLat hBox
  have hc := (GeneralPaperBasisCacheSize.cache_H k hm dict v S h N betaN initialGrid hj state inv).1
  exact hs.mono ((binaryWordWidth_mono (Nat.mul_le_mul_left N hc)).trans (binaryWordWidth_mul N (prepare m k).H))

def velocityWidth (m k j : ℕ) : ℕ :=
  binaryWordWidth (j*(prepare m k).H*(m+1))+binaryWordWidth (prepare m k).H

theorem velocity_width_bound (m k j : ℕ) :
    velocityWidth m k j≤binaryWordWidth j+2*binaryWordWidth (prepare m k).H+binaryWordWidth (m+1) := by
  have h1 := binaryWordWidth_mul (j*(prepare m k).H) (m+1)
  have h2 := binaryWordWidth_mul j (prepare m k).H
  unfold velocityWidth
  omega

theorem direction_height {T m j : ℕ} (k : ℕ) (hm : 0<m) (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (hj : j≤m*((prepare m k).K-1)) (state : GeneralPaperBasisState.State j (m*((prepare m k).K-1)))
    (inv : Invariant dict v S h N betaN initialGrid hj state)
    (next : Fin (m*((prepare m k).K-1))) (hNext : next.val=j) (a : Fin (m*((prepare m k).K-1))) :
    RationalHeight ((GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows next).velocity.read a)
      (velocityWidth m k j) := by
  have hc := GeneralPaperBasisCacheSize.cache_H k hm dict v S h N betaN initialGrid hj state inv
  have hCol (i : Fin j) : ((GeneralPaperBasisDirection.columnRun state.rows next).1.read i).natAbs≤m+1 := by
    rw [GeneralPaperBasisDirection.column_read]
    exact GeneralPaperBasisRowSize.coefficient hm dict v S h N betaN initialGrid hj state inv i next
  by_cases ha : a.val<j
  · let i : Fin j := ⟨a.val,ha⟩
    have he : embed hj i=a := Fin.ext rfl
    rw [←he,GeneralPaperBasisDirection.first_read _ _ _ _ hj i,GeneralPaperBasisRationalSolve.read]
    simp only [Nat.cast_one,one_mul]
    have hn := GeneralPaperStoredProductSize.mulVec state.adjugate (GeneralPaperBasisDirection.columnRun state.rows next).1
      (prepare m k).H (m+1) hc.2 hCol i
    rw [mulVec_data] at hn
    exact ((int_height _ _ hn).div (int_height _ _ hc.1)).neg
  · have hp : 1≤velocityWidth m k j := by
      have hw := binaryWordWidth_pos (prepare m k).H
      unfold velocityWidth
      omega
    by_cases he : a.val=j
    · have heq : a=next := Fin.ext (he.trans hNext.symm)
      rw [heq,GeneralPaperBasisDirection.next_read _ _ _ _ hNext]
      exact (int_height 1 1 (by norm_num)).mono hp
    · rw [GeneralPaperBasisDirection.later_read _ _ _ _ a (by omega)]
      exact GeneralPaperQuantizedHeight.zero_height _ (by omega)

end Blotto.GeneralPaperBasisStageSize
