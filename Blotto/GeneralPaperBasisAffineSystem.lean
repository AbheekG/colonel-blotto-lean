import Blotto.GeneralPaperBasisAffineData

/-! The cached continuation products solve the retained equations at
EVERY real threshold, including endpoints at which other rows become
tight. These real observers are erased, not an inverse oracle.
-/
namespace Blotto.GeneralPaperBasisAffineSystem
open GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisFreshRHS
open GeneralPaperBasisAffineData GeneralPaperBasisIntegerCasts GeneralPaperBasisStoredCorrect
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def value {d : ℕ} (data : Data d) (gamma : ℝ) : Fin d → ℝ :=
  fun k => (data.constant.read k:ℝ)/(data.determinant:ℝ)+gamma*((data.slope.read k:ℝ)/(data.determinant:ℝ))

theorem cached_system {d : ℕ} (state : State d d) (hD : state.determinant≠0)
    (hValid : Valid state.determinant state.adjugate (minor state.rows (Nat.le_refl _))) (rhs : Vector d) :
    (realMatrix (minor state.rows (Nat.le_refl _))).mulVec
      (fun k => (((observe state.adjugate).mulVec rhs.read k:ℤ):ℝ)/(state.determinant:ℝ))=realVector rhs.read := by
  have hh := GeneralPaperBasisRationalSolveSound.system 1 (by decide) state.determinant hD state.adjugate
    (minor state.rows (Nat.le_refl _)) hValid rhs
  unfold realVector
  simpa only [GeneralPaperBasisRationalSolve.read,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_intCast,
    Nat.cast_one,one_mul,div_one] using hh

theorem constant_system {d : ℕ} (state : State d d) (hD : state.determinant≠0)
    (hValid : Valid state.determinant state.adjugate (minor state.rows (Nat.le_refl _))) :
    (realMatrix (minor state.rows (Nat.le_refl _))).mulVec
      (fun k => ((prepare state).constant.read k:ℝ)/(state.determinant:ℝ))=
        fun i => ((state.rows.read i).constant:ℝ) := by
  have hh := cached_system state hD hValid (rhsRun state false).1
  unfold realVector at hh
  simpa only [constant_read,rhs_vector,Bool.false_eq_true,ite_false] using hh

theorem slope_system {d : ℕ} (state : State d d) (hD : state.determinant≠0)
    (hValid : Valid state.determinant state.adjugate (minor state.rows (Nat.le_refl _))) :
    (realMatrix (minor state.rows (Nat.le_refl _))).mulVec
      (fun k => ((prepare state).slope.read k:ℝ)/(state.determinant:ℝ))=
        fun i => ((state.rows.read i).slope:ℝ) := by
  have hh := cached_system state hD hValid (rhsRun state true).1
  unfold realVector at hh
  simpa only [slope_read,rhs_vector,ite_true] using hh

theorem system {d : ℕ} (state : State d d) (hD : state.determinant≠0)
    (hValid : Valid state.determinant state.adjugate (minor state.rows (Nat.le_refl _))) (gamma : ℝ) :
    (realMatrix (minor state.rows (Nat.le_refl _))).mulVec (value (prepare state) gamma)=
      fun i => (state.rows.read i).constant+gamma*((state.rows.read i).slope:ℝ) := by
  change (realMatrix (minor state.rows (Nat.le_refl _))).mulVec
    ((fun k => ((prepare state).constant.read k:ℝ)/(state.determinant:ℝ))+
      gamma • (fun k => ((prepare state).slope.read k:ℝ)/(state.determinant:ℝ)))=_
  rw [Matrix.mulVec_add,Matrix.mulVec_smul,constant_system state hD hValid,slope_system state hD hValid]
  rfl

theorem row_system {d : ℕ} (state : State d d) (hD : state.determinant≠0)
    (hValid : Valid state.determinant state.adjugate (minor state.rows (Nat.le_refl _))) (gamma : ℝ) (i : Fin d) :
    GeneralPaperBasisFreshPointSound.rowValue (state.rows.read i) (value (prepare state) gamma)=
      (state.rows.read i).constant+gamma*((state.rows.read i).slope:ℝ) :=
  congrFun (system state hD hValid gamma) i

end Blotto.GeneralPaperBasisAffineSystem
