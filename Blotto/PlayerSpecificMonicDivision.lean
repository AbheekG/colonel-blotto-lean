import Blotto.PlayerSpecificPolynomialCancellation

/-! Executable polynomial long division with computed leading-term
cancellation and fuel equal to the dividend's stored length. Proof-level
uniqueness identifies the result with mathematical monic division. -/
namespace Blotto.PlayerSpecificMonicDivision
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialCancellation
set_option autoImplicit false
set_option maxHeartbeats 3500000

def loop (q : Data) : ℕ → Data → Data×Data
  | 0,p => ([],trim p)
  | fuel+1,p =>
    let current := trim p
    if current=[] ∨ current.length<q.length then ([],current) else
      let tail := loop q fuel (remainder current q)
      (trim (add (term current q) tail.1),tail.2)

theorem reconstruction (q : Data) (fuel : ℕ) (p : Data) :
    semantics q*semantics (loop q fuel p).1+semantics (loop q fuel p).2=semantics p := by
  induction fuel generalizing p with
  | zero => simp only [loop,semantics,mul_zero,zero_add,trim_semantics]
  | succ fuel ih =>
    rw [loop]
    split
    · simp only [semantics,mul_zero,zero_add,trim_semantics]
    · simp only [trim_semantics,add_semantics]
      calc
        _ = semantics q*semantics (term (trim p) q)+
            (semantics q*semantics (loop q fuel (remainder (trim p) q)).1+
              semantics (loop q fuel (remainder (trim p) q)).2) := by ring
        _ = _ := by rw [ih,remainder_semantics,trim_semantics]; ring

theorem remainder_normalized (q : Data) (fuel : ℕ) (p : Data) : Normalized (loop q fuel p).2 := by
  induction fuel generalizing p with
  | zero => exact trim_normalized p
  | succ fuel ih => rw [loop]; split; exact trim_normalized p; exact ih _

theorem remainder_length (q : Data) (fuel : ℕ) (p : Data) (hq : Normalized q)
    (hm : (semantics q).Monic) (hp : p.length≤fuel) : (loop q fuel p).2.length<q.length := by
  have hq0 : q≠[] := by intro h; apply hm.ne_zero; rw [h]; rfl
  have hqpos := List.length_pos_iff.mpr hq0
  induction fuel generalizing p with
  | zero =>
    have hz : p=[] := List.length_eq_zero_iff.mp (by omega)
    subst p
    exact hqpos
  | succ fuel ih =>
    rw [loop]
    split
    · rename_i hstop
      rcases hstop with hz | hlt
      · rw [hz,List.length_nil]
        exact hqpos
      · exact hlt
    · rename_i hcontinue
      have hdrop := drops_length (trim p) q (trim_normalized p) hq (not_or.mp hcontinue).1 hm
        (le_of_not_gt (not_or.mp hcontinue).2)
      have htrim := trim_length p
      exact ih (remainder (trim p) q) (by omega)

theorem degree_lt_of_length (p q : Data) (hp : Normalized p) (hq : Normalized q)
    (hm : (semantics q).Monic) (hlen : p.length<q.length) : (semantics p).degree<(semantics q).degree := by
  have hq0 : q≠[] := by intro h; apply hm.ne_zero; rw [h]; rfl
  by_cases hp0 : p=[]
  · rw [hp0,semantics,Polynomial.degree_zero,Polynomial.degree_eq_natDegree hm.ne_zero]
    exact WithBot.bot_lt_coe _
  · rw [Polynomial.degree_eq_natDegree (nonzero p hp hp0),Polynomial.degree_eq_natDegree hm.ne_zero,Nat.cast_lt,
      degree_eq p hp hp0,degree_eq q hq hq0]
    have hpos := List.length_pos_iff.mpr hp0
    omega

def run (p q : Data) : Data×Data := loop q p.length p

theorem refines (p q : Data) (hq : Normalized q) (hm : (semantics q).Monic) :
    (semantics p /ₘ semantics q)=semantics (run p q).1 ∧
      (semantics p %ₘ semantics q)=semantics (run p q).2 := by
  have hr := reconstruction q p.length p
  have hlen := remainder_length q p.length p hq hm le_rfl
  have hdeg := degree_lt_of_length (loop q p.length p).2 q (remainder_normalized q p.length p) hq hm hlen
  exact Polynomial.div_modByMonic_unique _ _ hm ⟨by rw [add_comm]; exact hr,hdeg⟩

end Blotto.PlayerSpecificMonicDivision
