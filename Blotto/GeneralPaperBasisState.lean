import Blotto.GeneralPaperBasisEndpointRecompute

/-! Executed retained-basis state and one original-row extension. The
point and velocity arrays are each computed once before the ray search;
the same prepared score matrix is passed through the outer controller.
-/
namespace Blotto.GeneralPaperBasisState
open RationalOrderCell GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS
open GeneralPaperBasisDenseRow GeneralPaperBasisOriginalDirection
set_option autoImplicit false

structure State (j d : ℕ) where
  rows : Rows j d
  determinant : ℤ
  adjugate : IntMatrix j

def initial (d : ℕ) : State 0 d :=
  ⟨FixedArrayTable.ofFn (fun i => Fin.elim0 i),GeneralPaperBasisStoredCorrect.initial.1,
    GeneralPaperBasisStoredCorrect.initial.2⟩

def next {j d : ℕ} (hj : j<d) : Fin d := ⟨j,hj⟩

def advance {T m K j : ℕ} (labels : Fin T → Fin m → Fin K) (state : State j (m*(K-1)))
    (hj : j<m*(K-1)) (answer : GeneralPaperRayEndpoint.Answer T m K) : State (j+1) (m*(K-1)) :=
  let row := build (GeneralPaperRayBlockerRows.row labels answer.blocker)
  let u := GeneralPaperBasisDirection.columnRun state.rows (next hj)
  let v := rowPrefix row (Nat.le_of_lt hj)
  let updated := GeneralPaperBasisStoredStep.run state.determinant state.adjugate u.1 v (row.coefficients.read (next hj))
  ⟨GeneralPaperBasisAppendRows.append state.rows row,updated.determinant,updated.adjugate⟩

def step {T m K j : ℕ} (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h N : ℕ) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1))) (state : State j (m*(K-1))) (hj : j<m*(K-1)) :
    Option (State (j+1) (m*(K-1))) :=
  let point := GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid
  let velocity := GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)
  (GeneralPaperRayEndpoint.prepared labels matrix S h ((betaN:ℚ)/(N:ℚ)) (reader point.point) (reader velocity.velocity)).map
    (advance labels state hj)

end Blotto.GeneralPaperBasisState
