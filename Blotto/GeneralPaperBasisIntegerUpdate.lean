import Blotto.GeneralPaperBasisIntegerCasts

/-! Literal integer block update. Every displayed division is proved exact,
including negative nonzero determinants. No determinant/adjugate is computed
by the update program; they occur only in its correctness theorem.
-/
namespace Blotto.GeneralPaperBasisIntegerUpdate
open GeneralPaperBasisBorder GeneralPaperBasisAdjugateBlock GeneralPaperBasisIntegerCasts
set_option autoImplicit false
set_option maxHeartbeats 3500000

def update {i : Type*} (D Dnext : ℤ) (A : Matrix i i ℤ) (au va : i → ℤ) : Matrix (Option i) (Option i) ℤ :=
  border (fun j k => (Dnext*A j k+au j*va k)/D) (fun j => -au j) (fun k => -va k) D

theorem real_candidate {i : Type*} [Fintype i] [DecidableEq i] (M : Matrix i i ℤ)
    (u v : i → ℤ) (a : ℤ) (hDet : M.det≠0) (hNext : determinantUpdate M.det M.adjugate u v a≠0) :
    candidate (M.det:ℝ) ((determinantUpdate M.det M.adjugate u v a:ℤ):ℝ) (realMatrix M.adjugate)
      (realVector (M.adjugate.mulVec u)) (realVector (rowProduct v M.adjugate))=
        realMatrix (border M u v a).adjugate := by
  have hd : (realMatrix M).det≠0 := by rw [←det_cast]; exact_mod_cast hDet
  have hn : determinantUpdate (realMatrix M).det (realMatrix M).adjugate (realVector u) (realVector v) (a:ℝ)≠0 := by
    rw [←det_cast,←adjugate_cast,←update_cast]
    exact_mod_cast hNext
  have hh := GeneralPaperBasisBlockIdentity.adjugate_formula (realMatrix M) (realVector u) (realVector v) (a:ℝ) hd hn
  rw [←det_cast M,←adjugate_cast M,←update_cast,←mulVec_cast,←rowProduct_cast,←border_cast,←adjugate_cast] at hh
  exact hh

theorem exact_numerator {i : Type*} [Fintype i] [DecidableEq i] (M : Matrix i i ℤ)
    (u v : i → ℤ) (a : ℤ) (hDet : M.det≠0) (hNext : determinantUpdate M.det M.adjugate u v a≠0)
    (j k : i) :
    determinantUpdate M.det M.adjugate u v a*M.adjugate j k+
      (M.adjugate.mulVec u j)*(rowProduct v M.adjugate k)=
        (border M u v a).adjugate (some j) (some k)*M.det := by
  have hh := congrFun (congrFun (real_candidate M u v a hDet hNext) (some j)) (some k)
  change (((determinantUpdate M.det M.adjugate u v a:ℤ):ℝ)*(M.adjugate j k:ℝ)+
    ((M.adjugate.mulVec u j:ℤ):ℝ)*((rowProduct v M.adjugate k:ℤ):ℝ))/(M.det:ℝ)=
      ((border M u v a).adjugate (some j) (some k):ℝ) at hh
  have hd : (M.det:ℝ)≠0 := by exact_mod_cast hDet
  have he := (div_eq_iff hd).mp hh
  exact_mod_cast he

theorem update_correct {i : Type*} [Fintype i] [DecidableEq i] (M : Matrix i i ℤ)
    (u v : i → ℤ) (a : ℤ) (hDet : M.det≠0) (hNext : determinantUpdate M.det M.adjugate u v a≠0) :
    update M.det (determinantUpdate M.det M.adjugate u v a) M.adjugate
      (M.adjugate.mulVec u) (rowProduct v M.adjugate)=(border M u v a).adjugate := by
  have hR := real_candidate M u v a hDet hNext
  ext j k
  cases j with
  | none =>
    cases k with
    | none =>
      have hh := congrFun (congrFun hR none) none
      change (M.det:ℝ)=((border M u v a).adjugate none none:ℝ) at hh
      exact_mod_cast hh
    | some k =>
      have hh := congrFun (congrFun hR none) (some k)
      change -((rowProduct v M.adjugate k:ℤ):ℝ)=((border M u v a).adjugate none (some k):ℝ) at hh
      exact_mod_cast hh
  | some j =>
    cases k with
    | none =>
      have hh := congrFun (congrFun hR (some j)) none
      change -((M.adjugate.mulVec u j:ℤ):ℝ)=((border M u v a).adjugate (some j) none:ℝ) at hh
      exact_mod_cast hh
    | some k =>
      exact Int.ediv_eq_of_eq_mul_left hDet (exact_numerator M u v a hDet hNext j k)

end Blotto.GeneralPaperBasisIntegerUpdate
