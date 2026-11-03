import Blotto.GeneralPaperBasisFromGrid

/-! The executed final state is a full nonsingular original constraint
basis, tight at its feasible freshly solved point. Its retained equations
have exactly one real solution; no full-dimensionality assumption enters.
-/
namespace Blotto.GeneralPaperBasisFull
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperStrictScore
open GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisInvariant
open GeneralPaperBasisCoordinates GeneralPaperBasisFreshRHS GeneralPaperBasisFreshPointSound
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem nonsingular {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1))) (state : State (m*(K-1)) (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) :
    (minor state.rows (Nat.le_refl _)).det≠0 := by
  rw [←inv.cache.1]
  exact inv.nonzero

theorem original_tight {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (betaN : ℤ) (initialGrid : Vector (m*(K-1))) (state : State (m*(K-1)) (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) (i : Fin (m*(K-1))) :
    ∃ r : Index T m K (score v S) h,
      state.rows.read i=GeneralPaperBasisDenseRow.build (constraints dict.label (score v S) h r) ∧
        (constraints dict.label (score v S) h r).linear.evaluate
          (fun a => values N betaN state.determinant state.adjugate state.rows initialGrid (index a))=
          (constraints dict.label (score v S) h r).bound ((betaN:ℝ)/(N:ℝ)) := by
  obtain ⟨r,hr⟩ := inv.original i
  refine ⟨r,hr,?_⟩
  have hh := retained_rows N hN betaN state.determinant inv.nonzero state.adjugate state.rows initialGrid
    (Nat.le_refl _) inv.cache i
  rw [hr] at hh
  unfold rowValue at hh
  rw [GeneralPaperBasisDenseRow.build_evaluate] at hh
  simpa only [bound,Row.bound,GeneralPaperBasisDenseRow.build_constant,GeneralPaperBasisDenseRow.build_slope] using hh

theorem unique_real_point {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (betaN : ℤ) (initialGrid : Vector (m*(K-1))) (state : State (m*(K-1)) (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state)
    (x : Fin (m*(K-1)) → ℝ)
    (hRows : ∀ i,rowValue (state.rows.read i) x=bound (state.rows.read i) N betaN) :
    x=values N betaN state.determinant state.adjugate state.rows initialGrid := by
  apply GeneralPaperBasisFreshPointUnique.unique N hN betaN state.determinant inv.nonzero state.adjugate
    state.rows initialGrid (Nat.le_refl _) inv.cache x hRows
  intro k hk
  exact (Nat.not_le_of_gt k.isLt hk).elim

end Blotto.GeneralPaperBasisFull
