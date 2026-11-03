import Blotto.PlayerSpecificPolynomialNormalization

/-! Executable cancellation of one leading term against a monic rational
divisor. The checked strict degree drop supplies the fuel bound for actual
division, rather than a caller-provided termination or remainder oracle. -/
namespace Blotto.PlayerSpecificPolynomialCancellation
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization
set_option autoImplicit false
set_option maxHeartbeats 3500000

def monomial : ℕ → ℚ → Data
  | 0,a => [a]
  | n+1,a => 0::monomial n a

theorem monomial_semantics (n : ℕ) (a : ℚ) :
    semantics (monomial n a)=Polynomial.C a*Polynomial.X^n := by
  induction n with
  | zero => simp only [monomial,semantics,mul_zero,add_zero,pow_zero,mul_one]
  | succ n ih => simp only [monomial,semantics,map_zero,zero_add,ih,pow_succ]; ring

def term (p q : Data) : Data := monomial (p.length-q.length) (p.getLast?.getD 0)
def remainder (p q : Data) : Data := trim (subtract p (multiply q (term p q)))

theorem remainder_semantics (p q : Data) :
    semantics (remainder p q)=semantics p-semantics q*semantics (term p q) := by
  rw [remainder,trim_semantics,subtract_semantics,multiply_semantics]

theorem drops_degree (p q : Data) (hp : Normalized p) (hq : Normalized q)
    (hp0 : p≠[]) (hmonic : (semantics q).Monic) (hlen : q.length≤p.length) :
    (semantics (remainder p q)).degree<(semantics p).degree := by
  have hpne := nonzero p hp hp0
  have hqne := hmonic.ne_zero
  have hq0 : q≠[] := by intro hz; apply hqne; rw [hz]; rfl
  have hqpos : 0<q.length := List.length_pos_iff.mpr hq0
  have hppos : 0<p.length := List.length_pos_iff.mpr hp0
  have hNat : (semantics q).natDegree≤(semantics p).natDegree := by
    rw [degree_eq q hq hq0,degree_eq p hp hp0]
    omega
  have hDegree : (semantics q).degree≤(semantics p).degree := by
    rw [Polynomial.degree_eq_natDegree hqne,Polynomial.degree_eq_natDegree hpne,Nat.cast_le]
    exact hNat
  have he : p.length-q.length=(semantics p).natDegree-(semantics q).natDegree := by
    rw [degree_eq p hp hp0,degree_eq q hq hq0]
    omega
  rw [remainder_semantics,term,monomial_semantics,he,← leading_coefficient p hp hp0]
  exact Polynomial.div_wf_lemma ⟨hDegree,hpne⟩ hmonic

theorem drops_length (p q : Data) (hp : Normalized p) (hq : Normalized q)
    (hp0 : p≠[]) (hmonic : (semantics q).Monic) (hlen : q.length≤p.length) :
    (remainder p q).length<p.length := by
  have hn : Normalized (remainder p q) := trim_normalized _
  by_cases hr : remainder p q=[]
  · rw [hr,List.length_nil]
    exact List.length_pos_iff.mpr hp0
  · have hd := drops_degree p q hp hq hp0 hmonic hlen
    rw [Polynomial.degree_eq_natDegree (nonzero _ hn hr),Polynomial.degree_eq_natDegree (nonzero p hp hp0),Nat.cast_lt,
      degree_eq _ hn hr,degree_eq p hp hp0] at hd
    omega

end Blotto.PlayerSpecificPolynomialCancellation
