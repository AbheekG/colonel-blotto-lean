import Blotto.GeneralPaperTransferActualResidualPaths

/-! Executed N,tau,beta_aux controls for the original-basis initializer.
The displayed proxy integers p,q may be unreduced. The quotient depth is
constructed by doubling and admits bids equal to one. Bit/space prices and
the original active-basis search remain separate joins.
-/
namespace Blotto.GeneralPaperInitializerParameters
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Parameters where
  N : ℕ
  depth : ℕ
  beta : ℚ
  tau : ℚ
  auxiliary : ℚ
  work : ℕ

def prepare (m H p q : ℕ) (reciprocal : Bool) : Parameters :=
  let N := 4*m*H*p*q
  let scale := GeneralPaperPowerCeiling.ceiling N
  let beta : ℚ := if reciprocal then (q:ℚ)/p else (p:ℚ)/q
  let tau : ℚ := (m:ℚ)/N
  ⟨N,scale.doublings+1,beta,tau,beta-tau,scale.work+64⟩

theorem data (m H p q : ℕ) (reciprocal : Bool) :
    (prepare m H p q reciprocal).N=4*m*H*p*q ∧
    (prepare m H p q reciprocal).beta=(if reciprocal then (q:ℚ)/p else (p:ℚ)/q) ∧
    (prepare m H p q reciprocal).tau=(m:ℚ)/(prepare m H p q reciprocal).N ∧
    (prepare m H p q reciprocal).auxiliary=(prepare m H p q reciprocal).beta-(prepare m H p q reciprocal).tau :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem N_positive (m H p q : ℕ) (reciprocal : Bool) (hm : 0<m) (hH : 0<H) (hp : 0<p) (hq : 0<q) :
    0<(prepare m H p q reciprocal).N := by rw [(data m H p q reciprocal).1]; positivity

theorem tau_positive (m H p q : ℕ) (reciprocal : Bool) (hm : 0<m) (hH : 0<H) (hp : 0<p) (hq : 0<q) :
    0<(prepare m H p q reciprocal).tau := by
  rw [(data m H p q reciprocal).2.2.1]
  exact div_pos (by exact_mod_cast hm) (by exact_mod_cast N_positive m H p q reciprocal hm hH hp hq)

theorem tau_exact (m H p q : ℕ) (reciprocal : Bool) (hm : 0<m) :
    (prepare m H p q reciprocal).tau=1/(4*(H:ℚ)*p*q) := by
  have hmn : (m:ℚ)≠0 := by exact_mod_cast hm.ne'
  change (m:ℚ)/((4*m*H*p*q:ℕ):ℚ)=_
  push_cast
  field_simp

theorem scaled_budget (m H p q : ℕ) (reciprocal : Bool) (hp : 0<p) (hq : 0<q) :
    (prepare m H p q reciprocal).beta*((prepare m H p q reciprocal).N:ℚ)=
      ((4*m*H*(if reciprocal then q*q else p*p):ℕ):ℚ) := by
  have hpq : (p:ℚ)≠0 := by exact_mod_cast hp.ne'
  have hqq : (q:ℚ)≠0 := by exact_mod_cast hq.ne'
  cases reciprocal <;> simp only [prepare,Bool.false_eq_true,ite_false,ite_true,Nat.cast_mul,Nat.cast_ofNat]
  all_goals field_simp

theorem budget_dominates_tau (m H p q : ℕ) (reciprocal : Bool)
    (hm : 0<m) (hH : 0<H) (hp : 0<p) (hq : 0<q) :
    4*(prepare m H p q reciprocal).tau≤(prepare m H p q reciprocal).beta := by
  have hN : (0:ℚ)<(prepare m H p q reciprocal).N := by exact_mod_cast N_positive m H p q reciprocal hm hH hp hq
  have hs := scaled_budget m H p q reciprocal hp hq
  have hi : 4*m≤4*m*H*(if reciprocal then q*q else p*p) := by
    have hf : 1≤H*(if reciprocal then q*q else p*p) := by cases reciprocal <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> nlinarith
    nlinarith
  have hiq : (4:ℚ)*m≤((4*m*H*(if reciprocal then q*q else p*p):ℕ):ℚ) := by exact_mod_cast hi
  have ht : (prepare m H p q reciprocal).tau*((prepare m H p q reciprocal).N:ℚ)=(m:ℚ) := by
    rw [(data m H p q reciprocal).2.2.1]
    exact div_mul_cancel₀ _ hN.ne'
  nlinarith only [hs,hiq,ht,hN]

theorem auxiliary_positive (m H p q : ℕ) (reciprocal : Bool)
    (hm : 0<m) (hH : 0<H) (hp : 0<p) (hq : 0<q) : 0<(prepare m H p q reciprocal).auxiliary := by
  have ht := tau_positive m H p q reciprocal hm hH hp hq
  have hb := budget_dominates_tau m H p q reciprocal hm hH hp hq
  rw [(data m H p q reciprocal).2.2.2]
  linarith only [ht,hb]

theorem quotient_cap (m H p q : ℕ) (reciprocal : Bool) :
    (prepare m H p q reciprocal).N<2^(prepare m H p q reciprocal).depth := by
  have hl := GeneralPaperPowerCeiling.ceiling_lower (4*m*H*p*q)
  have hp := GeneralPaperPowerCeiling.ceiling_power (4*m*H*p*q)
  change 4*m*H*p*q<2^((GeneralPaperPowerCeiling.ceiling (4*m*H*p*q)).doublings+1)
  exact (hl.trans_eq hp).trans_lt (GeneralPaperBoundedQuotient.dyadic_cap _)

theorem prepare_work (m H p q : ℕ) (reciprocal : Bool) :
    (prepare m H p q reciprocal).work≤12*binaryWordWidth (prepare m H p q reciprocal).N+66 := by
  have hw := GeneralPaperPowerCeiling.ceiling_work (4*m*H*p*q)
  change (GeneralPaperPowerCeiling.ceiling (4*m*H*p*q)).work+64≤12*binaryWordWidth (4*m*H*p*q)+66
  omega

end Blotto.GeneralPaperInitializerParameters
