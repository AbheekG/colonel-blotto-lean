import Blotto.GeneralPaperSourceBasis

/-! Erased original-row witnesses identify the actually returned full
basis with the original variable-indexed subsystem used by the root and
bordered-determinant proofs. Runtime does not construct this inverse map.
-/
namespace Blotto.GeneralPaperBasisSelectedRows
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperStrictScore
open GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisInvariant
open GeneralPaperBasisCoordinates GeneralPaperBasisFreshRHS
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def selected {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1))) (state : State (m*(K-1)) (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) :
    Variable m K → Index T m K (score v S) h :=
  fun a => Classical.choose (inv.original (index a))

theorem selected_row {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1))) (state : State (m*(K-1)) (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) (a : Variable m K) :
    state.rows.read (index a)=GeneralPaperBasisDenseRow.build
      (constraints dict.label (score v S) h (selected dict v S h N betaN initialGrid state inv a)) :=
  Classical.choose_spec (inv.original (index a))

theorem matrix_identity {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1))) (state : State (m*(K-1)) (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) :
    GeneralPaperTransferMatrices.matrix dict.label (score v S) h (selected dict v S h N betaN initialGrid state inv)=
      (minor state.rows (Nat.le_refl _)).submatrix index index := by
  ext a c
  change (constraints dict.label (score v S) h (selected dict v S h N betaN initialGrid state inv a)).coefficient c=
    (state.rows.read (index a)).coefficients.read (index c)
  rw [selected_row,GeneralPaperBasisDenseRow.build_read]

theorem determinant_identity {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1))) (state : State (m*(K-1)) (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) :
    (GeneralPaperTransferMatrices.matrix dict.label (score v S) h (selected dict v S h N betaN initialGrid state inv)).det=
      state.determinant := by
  rw [matrix_identity]
  have hh := Matrix.det_submatrix_equiv_self (equivalence m K) (minor state.rows (Nat.le_refl _))
  exact hh.trans inv.cache.1.symm

end Blotto.GeneralPaperBasisSelectedRows
