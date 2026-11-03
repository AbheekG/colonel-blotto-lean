import Blotto.GeneralPaperProxyQuotientPrice

/-! Integer refinement of the actual adaptive quotient used by the CF
loop. Every early stop, quotient/remainder, depth and work field agrees with
the rational native routine. No built-in division/modulus is executed.
-/
namespace Blotto.GeneralPaperNaturalGrowingQuotient
set_option autoImplicit false
set_option maxHeartbeats 4000000

structure Result where
  quotient : ℕ
  remainder : ℕ
  depth : ℕ
  work : ℕ

def run (n a : ℕ) : ℕ → Result
  | 0 => ⟨0,n,0,4⟩
  | fuel+1 =>
    if n<a then ⟨0,n,0,4⟩ else
      let higher := run n (2*a) fuel
      if a≤higher.remainder then
        ⟨2*higher.quotient+1,higher.remainder-a,higher.depth+1,higher.work+14⟩
      else ⟨2*higher.quotient,higher.remainder,higher.depth+1,higher.work+14⟩

def lift (r : Result) : GeneralPaperGrowingQuotient.Result :=
  ⟨r.quotient,(r.remainder:ℚ),r.depth,r.work⟩

theorem data (n a fuel : ℕ) : lift (run n a fuel)=GeneralPaperGrowingQuotient.run (n:ℚ) (a:ℚ) fuel := by
  induction fuel generalizing a with
  | zero => rfl
  | succ fuel ih =>
    rw [run,GeneralPaperGrowingQuotient.run]
    by_cases h : n<a
    · have hRat : (n:ℚ)<(a:ℚ) := by exact_mod_cast h
      simp only [ite_eq_left h,ite_eq_left hRat,lift]
    · have hRat : ¬(n:ℚ)<(a:ℚ) := by exact_mod_cast h
      simp only [ite_eq_right h,ite_eq_right hRat]
      have hDouble : ((2*a:ℕ):ℚ)=2*(a:ℚ) := by push_cast; rfl
      rw [←hDouble,←ih (2*a)]
      dsimp only [lift]
      by_cases hBit : a≤(run n (2*a) fuel).remainder
      · have hReal : (a:ℚ)≤((run n (2*a) fuel).remainder:ℚ) := by exact_mod_cast hBit
        simp only [ite_eq_left hBit,Nat.cast_sub hBit]
        exact (ite_eq_left hReal).symm
      · have hReal : ¬(a:ℚ)≤((run n (2*a) fuel).remainder:ℚ) := by exact_mod_cast hBit
        simp only [ite_eq_right hBit]
        exact (ite_eq_right hReal).symm

theorem invariant (n a fuel : ℕ) :
    n=a*(run n a fuel).quotient+(run n a fuel).remainder := by
  induction fuel generalizing a with
  | zero => simp only [run,Nat.mul_zero,Nat.zero_add]
  | succ fuel ih =>
    rw [run]
    split
    · simp only [Nat.mul_zero,Nat.zero_add]
    · have hi := ih (2*a)
      dsimp only
      split
      · rename_i hBit
        have hRem : (run n (2*a) fuel).remainder-a+a=(run n (2*a) fuel).remainder := by omega
        nlinarith only [hi,hRem]
      · nlinarith only [hi]

theorem operand_bounds (n a fuel : ℕ) (ha : 0<a) :
    (run n a fuel).quotient≤n ∧ (run n a fuel).remainder≤n ∧ a*(run n a fuel).quotient≤n := by
  have hi := invariant n a fuel
  have hq : (run n a fuel).quotient≤a*(run n a fuel).quotient := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (run n a fuel).quotient (show 1≤a by omega)
  omega

theorem counters (n a fuel : ℕ) : (run n a fuel).work=14*(run n a fuel).depth+4 ∧ (run n a fuel).depth≤fuel := by
  have hd := congrArg GeneralPaperGrowingQuotient.Result.depth (data n a fuel)
  have hw := congrArg GeneralPaperGrowingQuotient.Result.work (data n a fuel)
  dsimp only [lift] at hd hw
  rw [hw,hd]
  exact ⟨GeneralPaperGrowingQuotient.run_work _ _ _,GeneralPaperGrowingQuotient.depth_le_fuel _ _ _⟩

end Blotto.GeneralPaperNaturalGrowingQuotient
