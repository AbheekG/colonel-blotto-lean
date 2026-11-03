import Blotto.GeneralPaperCachedClassifier

/-! The existing bounded rational quotient executes exactly the real
classifier quotient on rational inputs. This identifies the full result,
including remainder and work, without invoking a floor or real encoding.
-/
namespace Blotto.GeneralPaperProxyQuotientCast
set_option autoImplicit false

def lift (r : GeneralPaperBoundedQuotient.Result) : GeneralPaperProxyQuotient.Result :=
  ⟨r.quotient,(r.remainder:ℝ),r.work⟩

theorem data (x a : ℚ) (w : ℕ) :
    lift (GeneralPaperBoundedQuotient.run x a w)=GeneralPaperProxyQuotient.run (x:ℝ) (a:ℝ) w := by
  induction w generalizing a with
  | zero => rfl
  | succ w ih =>
    have hDouble : (2:ℝ)*(a:ℝ)=((2*a:ℚ):ℝ) := by push_cast; rfl
    rw [GeneralPaperBoundedQuotient.run,GeneralPaperProxyQuotient.run,hDouble,←ih (2*a)]
    dsimp only [lift]
    by_cases h : a≤(GeneralPaperBoundedQuotient.run x (2*a) w).remainder
    · have hReal : (a:ℝ)≤((GeneralPaperBoundedQuotient.run x (2*a) w).remainder:ℝ) := by exact_mod_cast h
      simp only [ite_eq_left h,Rat.cast_sub]
      exact (ite_eq_left hReal).symm
    · have hReal : ¬(a:ℝ)≤((GeneralPaperBoundedQuotient.run x (2*a) w).remainder:ℝ) := by exact_mod_cast h
      simp only [ite_eq_right h]
      exact (ite_eq_right hReal).symm

theorem locate_data (m k : ℕ) (b : ℚ) :
    lift (GeneralPaperBoundedQuotient.run (b*(GeneralPaperProxyParameters.prepare m k).Qg) 1
      ((GeneralPaperProxyParameters.prepare m k).gridBits+1))=GeneralPaperProxyQuotient.locate m k (b:ℝ) := by
  simpa only [GeneralPaperProxyQuotient.locate,Rat.cast_mul,Rat.cast_natCast,Rat.cast_one] using
    data (b*(GeneralPaperProxyParameters.prepare m k).Qg) 1 ((GeneralPaperProxyParameters.prepare m k).gridBits+1)

end Blotto.GeneralPaperProxyQuotientCast
