import Blotto.GeneralPaperBasisDirectionSound

/-! Original variable readers of stored packed arrays, and the exact
original-row to packed-Schur identity. The inverse coordinate map is
erased; every executed read uses the explicit arithmetic forward index.
-/
namespace Blotto.GeneralPaperBasisOriginalDirection
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS
open GeneralPaperBasisPrefixSum GeneralPaperBasisCoordinates GeneralPaperBasisDenseRow
open GeneralPaperBasisIntegerCasts GeneralPaperBasisStoredCorrect
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

def reader {m K : ℕ} (packed : GeneralPaperBasisRationalSolve.RatVector (m*(K-1))) : Variable m K → ℚ :=
  fun v => packed.read (index v)

def rowPrefix {j d : ℕ} (row : Dense d) (hj : j≤d) : Vector j :=
  FixedArrayTable.ofFn (fun i => row.coefficients.read (embed hj i))

theorem next_velocity {m K j : ℕ} (D : ℤ) (A : IntMatrix j) (rows : Rows j (m*(K-1)))
    (next : Fin (m*(K-1))) (hNext : next.val=j) :
    ∃ v : Variable m K,reader (GeneralPaperBasisDirection.run D A rows next).velocity v=1 := by
  obtain ⟨v,hv⟩ := index_surjective m K next
  refine ⟨v,?_⟩
  change (GeneralPaperBasisDirection.run D A rows next).velocity.read (index v)=1
  rw [hv]
  exact GeneralPaperBasisDirection.next_read D A rows next hNext

theorem retained_zero {m K j : ℕ} (D : ℤ) (hD : D≠0) (A : IntMatrix j) (rows : Rows j (m*(K-1)))
    (next : Fin (m*(K-1))) (hNext : next.val=j) (hj : j≤m*(K-1)) (hValid : Valid D A (minor rows hj))
    (i : Fin j) (r : Row (Variable m K)) (hRow : rows.read i=build r) :
    r.linear.evaluate (fun v => (reader (GeneralPaperBasisDirection.run D A rows next).velocity v:ℝ))=0 := by
  change r.linear.evaluate (fun v => GeneralPaperBasisDirectionSound.values D A rows next (index v))=0
  rw [←build_evaluate]
  rw [←hRow]
  exact GeneralPaperBasisDirectionSound.retained_zero D hD A rows next hNext hj hValid i

theorem schur_identity {m K j : ℕ} (D : ℤ) (A : IntMatrix j) (rows : Rows j (m*(K-1)))
    (next : Fin (m*(K-1))) (hNext : next.val=j) (hj : j≤m*(K-1)) (r : Row (Variable m K)) :
    r.linear.evaluate (fun v => (reader (GeneralPaperBasisDirection.run D A rows next).velocity v:ℝ))=
      ((GeneralPaperBasisBorder.border (realMatrix (minor rows hj))
        (realVector (GeneralPaperBasisDirection.columnRun rows next).1.read)
        (realVector (rowPrefix (build r) hj).read) ((build r).coefficients.read next:ℝ)).mulVec
          (GeneralPaperBasisBorder.direction (GeneralPaperBasisDirectionSound.solved D A rows next))) none := by
  change r.linear.evaluate (fun v => GeneralPaperBasisDirectionSound.values D A rows next (index v))=_
  rw [←build_evaluate,GeneralPaperBasisDirectionSound.dot D A rows next hNext hj (build r).coefficients,
    GeneralPaperBasisBorder.direction_new]
  simp only [realVector,rowPrefix,FixedArrayTable.read_ofFn]

end Blotto.GeneralPaperBasisOriginalDirection
