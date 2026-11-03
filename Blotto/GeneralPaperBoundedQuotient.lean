import Blotto.GeneralPaperComputedTransfer

/-! A bounded quotient from real-RAM arithmetic and comparisons. The
constructed depth w is supplied with the score scale, not extracted from an
original input encoding. The code doubles the divisor on descent and reads
the bits on return. Powers and floor occur only in the specification.
-/
namespace Blotto.GeneralPaperBoundedQuotient
set_option autoImplicit false
set_option maxHeartbeats 1500000

structure Result where
  quotient : ℕ
  remainder : ℚ
  work : ℕ

def run (x a : ℚ) : ℕ → Result
  | 0 => ⟨0,x,2⟩
  | w+1 =>
      let higher := run x (2*a) w
      if a≤higher.remainder then
        ⟨2*higher.quotient+1,higher.remainder-a,higher.work+12⟩
      else ⟨2*higher.quotient,higher.remainder,higher.work+12⟩

theorem run_spec (x a : ℚ) (ha : 0<a) (w : ℕ) (hx : 0≤x) (hCap : x<a*(2:ℚ)^w) :
    x=a*((run x a w).quotient:ℚ)+(run x a w).remainder ∧
      0≤(run x a w).remainder ∧ (run x a w).remainder<a := by
  induction w generalizing a with
  | zero =>
    change x=a*(0:ℚ)+x ∧ 0≤x ∧ x<a
    constructor
    · ring
    · exact ⟨hx,by simpa only [pow_zero,mul_one] using hCap⟩
  | succ w ih =>
    have hHigher : x<(2*a)*(2:ℚ)^w := by
      rw [pow_succ] at hCap
      nlinarith only [hCap]
    have hi := ih (2*a) (by positivity) hHigher
    unfold run
    dsimp only
    split
    · rename_i hBit
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
      constructor
      · nlinarith only [hi.1]
      · constructor <;> linarith only [hBit,hi.2.2]
    · rename_i hBit
      simp only [Nat.cast_mul,Nat.cast_ofNat]
      constructor
      · nlinarith only [hi.1]
      · exact ⟨hi.2.1,lt_of_not_ge hBit⟩

theorem run_work (x a : ℚ) (w : ℕ) : (run x a w).work=12*w+2 := by
  induction w generalizing a with
  | zero => rfl
  | succ w ih =>
    unfold run
    dsimp only
    split <;> simp only [ih] <;> omega

theorem run_floor (x : ℚ) (w : ℕ) (hx : 0≤x) (hCap : x<(2:ℚ)^w) :
    (run x 1 w).quotient=⌊x⌋₊ := by
  have hs := run_spec x 1 (by norm_num) w hx (by simpa only [one_mul] using hCap)
  have hlo : ((run x 1 w).quotient:ℚ)≤x := by linarith only [hs.1,hs.2.1]
  have hhi : x<((run x 1 w).quotient:ℚ)+1 := by linarith only [hs.1,hs.2.2]
  symm
  exact (Nat.floor_eq_iff hx).mpr ⟨hlo,hhi⟩

theorem dyadic_cap (s : ℕ) : (2:ℕ)^s<2^(s+1) := by
  have hp : 0<(2:ℕ)^s := pow_pos (by decide) s
  rw [pow_succ]
  omega

end Blotto.GeneralPaperBoundedQuotient
