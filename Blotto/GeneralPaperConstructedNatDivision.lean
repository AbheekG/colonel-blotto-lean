import Blotto.GeneralPaperGrowingQuotient

/-! Quotient and natural remainder of constructed integers from arithmetic
quotient construction. Nat division/modulus occur only in theorems; the
executed remainder is a multiplication and natural subtraction.
-/
namespace Blotto.GeneralPaperConstructedNatDivision
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result where
  quotient : ℕ
  remainder : ℕ
  depth : ℕ
  work : ℕ

def run (n d fuel : ℕ) : Result :=
  let found := GeneralPaperGrowingQuotient.run n d fuel
  ⟨found.quotient,n-d*found.quotient,found.depth,found.work+12⟩

theorem run_spec (n d fuel : ℕ) (hd : 0<d) (hCap : n<d*2^fuel) :
    n=d*(run n d fuel).quotient+(run n d fuel).remainder ∧ (run n d fuel).remainder<d := by
  have hdq : (0:ℚ)<d := by exact_mod_cast hd
  have hc : (n:ℚ)<(d:ℚ)*(2:ℚ)^fuel := by exact_mod_cast hCap
  have hs := GeneralPaperGrowingQuotient.run_spec n d hdq fuel (by positivity) hc
  have hProduct : d*(GeneralPaperGrowingQuotient.run n d fuel).quotient≤n := by
    have he : (d:ℚ)*((GeneralPaperGrowingQuotient.run n d fuel).quotient:ℚ)≤(n:ℚ) := by linarith only [hs.1,hs.2.1]
    exact_mod_cast he
  have hR : ((n-d*(GeneralPaperGrowingQuotient.run n d fuel).quotient:ℕ):ℚ)=(GeneralPaperGrowingQuotient.run n d fuel).remainder := by
    rw [Nat.cast_sub hProduct,Nat.cast_mul]
    linarith only [hs.1]
  constructor
  · dsimp only [run]
    omega
  · dsimp only [run]
    have he : ((n-d*(GeneralPaperGrowingQuotient.run n d fuel).quotient:ℕ):ℚ)<(d:ℚ) := by rw [hR]; exact hs.2.2
    exact_mod_cast he

theorem quotient_eq (n d fuel : ℕ) (hd : 0<d) (hCap : n<d*2^fuel) : (run n d fuel).quotient=n/d := by
  obtain ⟨he,hr⟩ := run_spec n d fuel hd hCap
  have hDivision := congrArg (fun v : ℕ => v/d) he
  rw [Nat.mul_add_div hd,Nat.div_eq_of_lt hr,Nat.add_zero] at hDivision
  exact hDivision.symm

theorem remainder_eq (n d fuel : ℕ) (hd : 0<d) (hCap : n<d*2^fuel) : (run n d fuel).remainder=n%d := by
  obtain ⟨he,hr⟩ := run_spec n d fuel hd hCap
  have hMod := congrArg (fun v : ℕ => v%d) he
  rw [Nat.mul_add_mod,Nat.mod_eq_of_lt hr] at hMod
  exact hMod.symm

theorem work_word_bound (n d fuel : ℕ) (hd : 0<d) (hCap : n<d*2^fuel) :
    (run n d fuel).work≤14*binaryWordWidth (run n d fuel).quotient+16 := by
  have he := GeneralPaperGrowingQuotient.work_word_bound n d (by exact_mod_cast hd) fuel (by positivity) (by exact_mod_cast hCap)
  dsimp only [run]
  omega

theorem work_depth (n d fuel : ℕ) : (run n d fuel).work=14*(run n d fuel).depth+16 := by
  dsimp only [run]
  rw [GeneralPaperGrowingQuotient.run_work]

theorem depth_le_fuel (n d fuel : ℕ) : (run n d fuel).depth≤fuel :=
  GeneralPaperGrowingQuotient.depth_le_fuel n d fuel

end Blotto.GeneralPaperConstructedNatDivision
