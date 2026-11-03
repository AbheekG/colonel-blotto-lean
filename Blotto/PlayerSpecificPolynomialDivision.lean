import Blotto.PlayerSpecificMonicDivision

/-! Arbitrary rational divisors are normalized numerically, divided by
their computed leading coefficient, and handled by executable monic long
division. This is total, including a zero divisor, and refines exact
polynomial division/remainder without a supplied arithmetic oracle. -/
namespace Blotto.PlayerSpecificPolynomialDivision
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization
set_option autoImplicit false
set_option maxHeartbeats 3500000

def inverseLead (q : Data) : ℚ := (q.getLast?.getD 0)⁻¹
def monicize (q : Data) : Data := trim (scale (inverseLead q) q)

theorem monicize_semantics (q : Data) (hq : Normalized q) (hq0 : q≠[]) :
    semantics (monicize q)=semantics q*Polynomial.C (semantics q).leadingCoeff⁻¹ := by
  rw [monicize,trim_semantics,scale_semantics,inverseLead,← leading_coefficient q hq hq0]
  exact mul_comm _ _

theorem monicize_monic (q : Data) (hq : Normalized q) (hq0 : q≠[]) : (semantics (monicize q)).Monic := by
  rw [monicize_semantics q hq hq0]
  exact Polynomial.monic_mul_leadingCoeff_inv (nonzero q hq hq0)

def run (p q : Data) : Data×Data :=
  let divisor := trim q
  if divisor=[] then ([],trim p) else
    let divided := PlayerSpecificMonicDivision.run p (monicize divisor)
    (trim (scale (inverseLead divisor) divided.1),divided.2)

theorem refines (p q : Data) :
    semantics p / semantics q=semantics (run p q).1 ∧
      semantics p % semantics q=semantics (run p q).2 := by
  unfold run
  dsimp only
  split
  · rename_i hz
    have hzero := (trim_nil_iff q).mp hz
    simp only [hzero,EuclideanDomain.div_zero,EuclideanDomain.mod_zero,semantics,trim_semantics,and_self]
  · rename_i hnonempty
    have hm := monicize_monic (trim q) (trim_normalized q) hnonempty
    have hr := PlayerSpecificMonicDivision.refines p (monicize (trim q)) (trim_normalized _) hm
    have hdata := monicize_semantics (trim q) (trim_normalized q) hnonempty
    have hlead := leading_coefficient (trim q) (trim_normalized q) hnonempty
    rw [trim_semantics] at hdata hlead
    constructor
    · rw [trim_semantics,scale_semantics,← hr.1,Polynomial.div_def,hdata,inverseLead,← hlead]
    · rw [← hr.2,Polynomial.mod_def,hdata]

theorem quotient_normalized (p q : Data) : Normalized (run p q).1 := by
  unfold run
  dsimp only
  split
  · exact Or.inl rfl
  · exact trim_normalized _

theorem remainder_normalized (p q : Data) : Normalized (run p q).2 := by
  unfold run
  dsimp only
  split
  · exact trim_normalized p
  · exact PlayerSpecificMonicDivision.remainder_normalized _ _ _

theorem reconstruction (p q : Data) :
    semantics q*semantics (run p q).1+semantics (run p q).2=semantics p := by
  rw [← (refines p q).1,← (refines p q).2]
  exact EuclideanDomain.div_add_mod _ _

theorem remainder_degree (p q : Data) (hq : semantics q≠0) :
    (semantics (run p q).2).degree<(semantics q).degree := by
  rw [← (refines p q).2]
  exact Polynomial.degree_mod_lt _ hq

theorem remainder_length (p q : Data) (hq : Normalized q) (hq0 : q≠[]) :
    (run p q).2.length<q.length := by
  have hd := remainder_degree p q (nonzero q hq hq0)
  by_cases hr : (run p q).2=[]
  · rw [hr,List.length_nil]
    exact List.length_pos_iff.mpr hq0
  · rw [Polynomial.degree_eq_natDegree (nonzero _ (remainder_normalized p q) hr),
      Polynomial.degree_eq_natDegree (nonzero q hq hq0),Nat.cast_lt,
      degree_eq _ (remainder_normalized p q) hr,degree_eq q hq hq0] at hd
    omega

end Blotto.PlayerSpecificPolynomialDivision
