import Blotto.PlayerSpecificPolynomialDivision

/-! The actual Euclidean algorithm over stored rational coefficients.
Each computed remainder is normalized and strictly shorter. A computed
fuel bound suffices, and the returned polynomial has exactly the common
divisors of the original pair. No GCD oracle is executed. -/
namespace Blotto.PlayerSpecificPolynomialGCD
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization
set_option autoImplicit false
set_option maxHeartbeats 3500000

def loop : ℕ → Data → Data → Data
  | 0,p,_ => trim p
  | fuel+1,p,q =>
    if q=[] then trim p else loop fuel q (PlayerSpecificPolynomialDivision.run p q).2

theorem normalized (fuel : ℕ) (p q : Data) : Normalized (loop fuel p q) := by
  induction fuel generalizing p q with
  | zero => exact trim_normalized p
  | succ fuel ih => rw [loop]; split; exact trim_normalized p; exact ih _ _

theorem common_divisors (fuel : ℕ) (p q : Data) (hq : Normalized q) (hcap : q.length≤fuel)
    (r : Polynomial ℚ) :
    r∣semantics (loop fuel p q) ↔ r∣semantics p ∧ r∣semantics q := by
  induction fuel generalizing p q with
  | zero =>
    have hz : q=[] := List.length_eq_zero_iff.mp (by omega)
    simp only [hz,loop,trim_semantics,semantics,dvd_zero,and_true]
  | succ fuel ih =>
    rw [loop]
    split
    · rename_i hz
      simp only [hz,trim_semantics,semantics,dvd_zero,and_true]
    · rename_i hnonempty
      have hdrop := PlayerSpecificPolynomialDivision.remainder_length p q hq hnonempty
      rw [ih q (PlayerSpecificPolynomialDivision.run p q).2
        (PlayerSpecificPolynomialDivision.remainder_normalized p q) (by omega),
        ← (PlayerSpecificPolynomialDivision.refines p q).2]
      constructor
      · rintro ⟨hq',hrem⟩
        exact ⟨(EuclideanDomain.dvd_mod_iff hq').mp hrem,hq'⟩
      · rintro ⟨hp',hq'⟩
        exact ⟨hq',(EuclideanDomain.dvd_mod_iff hq').mpr hp'⟩

def run (p q : Data) : Data :=
  let divisor := trim q
  loop divisor.length p divisor

theorem run_normalized (p q : Data) : Normalized (run p q) := normalized _ _ _

theorem run_common_divisors (p q : Data) (r : Polynomial ℚ) :
    r∣semantics (run p q) ↔ r∣semantics p ∧ r∣semantics q := by
  have h := common_divisors (trim q).length p (trim q) (trim_normalized q) le_rfl r
  simpa only [run,trim_semantics] using h

theorem divides_inputs (p q : Data) :
    semantics (run p q)∣semantics p ∧ semantics (run p q)∣semantics q :=
  (run_common_divisors p q _).mp dvd_rfl

theorem associated_gcd (p q : Data) :
    Associated (semantics (run p q)) (gcd (semantics p) (semantics q)) := by
  apply associated_of_dvd_dvd
  · exact dvd_gcd (divides_inputs p q).1 (divides_inputs p q).2
  · exact (run_common_divisors p q _).mpr ⟨gcd_dvd_left _ _,gcd_dvd_right _ _⟩

end Blotto.PlayerSpecificPolynomialGCD
