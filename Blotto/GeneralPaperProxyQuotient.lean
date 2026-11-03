import Blotto.GeneralPaperProxyRootQuery

/-! Original real budget access for the classifier. A bounded doubling and
comparison loop locates its root-grid cell. Runtime never asks for the real
input's encoding, numerator, denominator or floor. Rational implementation
prices and the remaining classifier comparisons are separate joins.
-/
namespace Blotto.GeneralPaperProxyQuotient
open GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 1500000

structure Result where
  quotient : ℕ
  remainder : ℝ
  work : ℕ

noncomputable def run (x a : ℝ) : ℕ → Result
  | 0 => ⟨0,x,2⟩
  | w+1 =>
      let higher := run x (2*a) w
      if a≤higher.remainder then
        ⟨2*higher.quotient+1,higher.remainder-a,higher.work+12⟩
      else ⟨2*higher.quotient,higher.remainder,higher.work+12⟩

theorem run_spec (x a : ℝ) (ha : 0<a) (w : ℕ) (hx : 0≤x) (hCap : x<a*(2:ℝ)^w) :
    x=a*((run x a w).quotient:ℝ)+(run x a w).remainder ∧
      0≤(run x a w).remainder ∧ (run x a w).remainder<a := by
  induction w generalizing a with
  | zero =>
    simp only [run,Nat.cast_zero]
    exact ⟨by ring,hx,by simpa only [pow_zero,mul_one] using hCap⟩
  | succ w ih =>
    have hh : x<(2*a)*(2:ℝ)^w := by rw [pow_succ] at hCap; nlinarith only [hCap]
    have hi := ih (2*a) (by positivity) hh
    unfold run
    dsimp only
    split
    · rename_i hb
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
      exact ⟨by nlinarith only [hi.1],by linarith only [hb],by linarith only [hi.2.2]⟩
    · rename_i hb
      simp only [Nat.cast_mul,Nat.cast_ofNat]
      exact ⟨by nlinarith only [hi.1],hi.2.1,lt_of_not_ge hb⟩

theorem run_work (x a : ℝ) (w : ℕ) : (run x a w).work=12*w+2 := by
  induction w generalizing a with
  | zero => rfl
  | succ w ih => unfold run; dsimp only; split <;> simp only [ih] <;> omega

noncomputable def locate (m k : ℕ) (b : ℝ) : Result :=
  run (b*((prepare m k).Qg:ℝ)) 1 ((prepare m k).gridBits+1)

theorem locate_spec (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    (locate m k b).quotient<(prepare m k).Qg ∧
      ((locate m k b).quotient:ℝ)/((prepare m k).Qg:ℝ)≤b ∧
      b<(((locate m k b).quotient:ℝ)+1)/((prepare m k).Qg:ℝ) := by
  let Q := (prepare m k).Qg
  have hQ : (0:ℝ)<Q := by exact_mod_cast grid_positive m k
  have hPow : (Q:ℝ)=(2:ℝ)^(prepare m k).gridBits := by exact_mod_cast grid_power m k
  have hx : b*(Q:ℝ)<(Q:ℝ) := by nlinarith only [hb.2,hQ]
  have hc : b*(Q:ℝ)<1*(2:ℝ)^((prepare m k).gridBits+1) := by
    rw [pow_succ,←hPow]
    nlinarith only [hx,hQ]
  have hs := run_spec (b*(Q:ℝ)) 1 (by norm_num) ((prepare m k).gridBits+1) (mul_nonneg hb.1.le hQ.le) hc
  change b*(Q:ℝ)=1*((locate m k b).quotient:ℝ)+(locate m k b).remainder ∧
    0≤(locate m k b).remainder ∧ (locate m k b).remainder<1 at hs
  have hj : ((locate m k b).quotient:ℝ)<(Q:ℝ) := by linarith only [hs.1,hs.2.1,hx]
  refine ⟨by exact_mod_cast hj,?_,?_⟩
  · apply (div_le_iff₀ hQ).mpr
    linarith only [hs.1,hs.2.1]
  · apply (lt_div_iff₀ hQ).mpr
    linarith only [hs.1,hs.2.2]

theorem locate_work (m k : ℕ) (b : ℝ) :
    (locate m k b).work=12*((prepare m k).gridBits+1)+2 := run_work _ _ _

end Blotto.GeneralPaperProxyQuotient
