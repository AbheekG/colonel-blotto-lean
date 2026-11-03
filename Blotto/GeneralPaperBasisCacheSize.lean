import Blotto.GeneralPaperIntegerDotSize

/-! At EVERY valid stage the actual cached determinant and every cached
adjugate entry have the original-row determinant envelope. Cramer bounds
also control the actual final affine products. No denominator history or
factorial is introduced by these bounds.
-/
namespace Blotto.GeneralPaperBasisCacheSize
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisInvariant
open GeneralPaperProxyParameters
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem determinant {T m K j : ℕ} (hm : 0<m) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1)))
    (hj : j≤m*(K-1)) (state : GeneralPaperBasisState.State j (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid hj state) :
    state.determinant.natAbs≤(m+1)^j := by
  rw [inv.cache.1]
  have hh := GeneralPaperIntegerMatrixSize.determinant (minor state.rows hj) (m+1) (fun i => by
    have hr := GeneralPaperBasisRowSize.minor_mass hm dict v S h N betaN initialGrid hj state inv i false
    omega)
  simpa only [Fintype.card_fin] using hh

theorem adjugate {T m K j : ℕ} (hm : 0<m) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1)))
    (hj : j≤m*(K-1)) (state : GeneralPaperBasisState.State j (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid hj state) (a b : Fin j) :
    ((state.adjugate.read a).read b).natAbs≤(m+1)^j := by
  change ((observe state.adjugate) a b).natAbs≤_
  rw [inv.cache.2]
  have hh := GeneralPaperIntegerMatrixSize.adjugate (minor state.rows hj) (m+1) (by omega) (fun i => by
    have hr := GeneralPaperBasisRowSize.minor_mass hm dict v S h N betaN initialGrid hj state inv i false
    omega) a b
  simpa only [Fintype.card_fin] using hh

theorem power_H (m k j : ℕ) (hj : j≤m*((prepare m k).K-1)) : (m+1)^j≤(prepare m k).H := by
  rw [(data m k).2.2.2.1,(data m k).2.2.1]
  exact (Nat.pow_le_pow_left (by omega : m+1≤m+3) j).trans
    (Nat.pow_le_pow_right (by omega : 0<m+3) (by omega))

theorem cache_H {T m j : ℕ} (k : ℕ) (hm : 0<m) (dict : GeneralPaperDictionary.Dictionary T m (prepare m k).K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (hj : j≤m*((prepare m k).K-1)) (state : GeneralPaperBasisState.State j (m*((prepare m k).K-1)))
    (inv : Invariant dict v S h N betaN initialGrid hj state) :
    state.determinant.natAbs≤(prepare m k).H ∧ ∀ a b,((state.adjugate.read a).read b).natAbs≤(prepare m k).H :=
  ⟨(determinant hm dict v S h N betaN initialGrid hj state inv).trans (power_H m k j hj),
    fun a b => (adjugate hm dict v S h N betaN initialGrid hj state inv a b).trans (power_H m k j hj)⟩

theorem rhs_product {T m K j : ℕ} (hm : 0<m) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1)))
    (hj : j≤m*(K-1)) (state : GeneralPaperBasisState.State j (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid hj state) (useSlope : Bool) (a : Fin j) :
    ((observe state.adjugate).mulVec (fun i => if useSlope then (state.rows.read i).slope else (state.rows.read i).constant) a).natAbs≤(m+1)^j := by
  rw [inv.cache.2]
  have hh := GeneralPaperIntegerMatrixSize.cramer (minor state.rows hj)
    (fun i => if useSlope then (state.rows.read i).slope else (state.rows.read i).constant) (m+1)
    (GeneralPaperBasisRowSize.minor_mass hm dict v S h N betaN initialGrid hj state inv · useSlope) a
  simpa only [Fintype.card_fin] using hh

theorem affine_products {T m K : ℕ} (hm : 0<m) (dict : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1)))
    (state : GeneralPaperBasisState.State (m*(K-1)) (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) (a : Fin (m*(K-1))) :
    ((GeneralPaperBasisAffineData.prepare state).constant.read a).natAbs≤(m+1)^(m*(K-1)) ∧
      ((GeneralPaperBasisAffineData.prepare state).slope.read a).natAbs≤(m+1)^(m*(K-1)) := by
  rw [GeneralPaperBasisAffineData.constant_read,GeneralPaperBasisAffineData.slope_read]
  exact ⟨rhs_product hm dict v S h N betaN initialGrid (Nat.le_refl _) state inv false a,
    rhs_product hm dict v S h N betaN initialGrid (Nat.le_refl _) state inv true a⟩

end Blotto.GeneralPaperBasisCacheSize
