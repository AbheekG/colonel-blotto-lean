import Blotto.GeneralPaperBasisFreshPoint

/-! The actual stored rational solve satisfies the retained prefix system.
The common N factor scales only the original right-hand side; no prior
point or temporary crossing denominator is used.
-/
namespace Blotto.GeneralPaperBasisRationalSolveSound
open GeneralPaperBasisStoredProducts GeneralPaperBasisIntegerCasts GeneralPaperBasisStoredCorrect
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem system {j : ℕ} (N : ℕ) (hN : 0<N) (D : ℤ) (hD : D≠0) (A : IntMatrix j)
    (M : Matrix (Fin j) (Fin j) ℤ) (hValid : Valid D A M) (rhs : Vector j) :
    (realMatrix M).mulVec (fun k => ((GeneralPaperBasisRationalSolve.run N D A rhs).values.read k:ℝ))=
      fun i => (rhs.read i:ℝ)/(N:ℝ) := by
  have hm : M*observe A=D • (1 : Matrix (Fin j) (Fin j) ℤ) := by
    rw [hValid.1,hValid.2]
    exact Matrix.mul_adjugate M
  have hv : M.mulVec ((observe A).mulVec rhs.read)=D • rhs.read := by
    rw [Matrix.mulVec_mulVec,hm,Matrix.smul_mulVec,Matrix.one_mulVec]
  have hCast := congrArg realVector hv
  rw [mulVec_cast] at hCast
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hd : (D:ℝ)≠0 := by exact_mod_cast hD
  funext i
  have hi := congrFun hCast i
  change (∑ k,(M i k:ℝ)*(((observe A).mulVec rhs.read k:ℤ):ℝ))=((D*rhs.read i:ℤ):ℝ) at hi
  rw [Int.cast_mul] at hi
  change (∑ k,(M i k:ℝ)*((GeneralPaperBasisRationalSolve.run N D A rhs).values.read k:ℝ))=_
  simp only [GeneralPaperBasisRationalSolve.read,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_intCast,
    ←mul_div_assoc,←Finset.sum_div]
  rw [hi]
  field_simp

end Blotto.GeneralPaperBasisRationalSolveSound
