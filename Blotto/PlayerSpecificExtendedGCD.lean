import Blotto.PlayerSpecificPolynomialGCD

/-! Extended Euclidean certificates computed by the same rational polynomial
divisions as the checked GCD. The returned coefficients reconstruct the
computed gcd for every fuel, and a coefficient-length fuel gives exactly the
common divisors of the inputs. -/
namespace Blotto.PlayerSpecificExtendedGCD
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Result where
  gcd : Data
  left : Data
  right : Data

def loop : ℕ → Data → Data → Result
  | 0,p,_ => ⟨trim p,[1],[]⟩
  | fuel+1,p,q =>
    if q=[] then ⟨trim p,[1],[]⟩ else
      let division := PlayerSpecificPolynomialDivision.run p q
      let rest := loop fuel q division.2
      ⟨rest.gcd,rest.right,trim (subtract rest.left (multiply division.1 rest.right))⟩

theorem gcd_eq (fuel : ℕ) (p q : Data) :
    (loop fuel p q).gcd=PlayerSpecificPolynomialGCD.loop fuel p q := by
  induction fuel generalizing p q with
  | zero => rfl
  | succ fuel ih =>
    simp only [loop,PlayerSpecificPolynomialGCD.loop]
    split
    · rfl
    · exact ih _ _

theorem identity (fuel : ℕ) (p q : Data) :
    semantics (loop fuel p q).gcd=
      semantics p*semantics (loop fuel p q).left+semantics q*semantics (loop fuel p q).right := by
  induction fuel generalizing p q with
  | zero => simp [loop,trim_semantics,semantics]
  | succ fuel ih =>
    rw [loop]
    split
    · simp [trim_semantics,semantics]
    · simp only [trim_semantics,subtract_semantics,multiply_semantics]
      rw [ih]
      have hr := PlayerSpecificPolynomialDivision.reconstruction p q
      linear_combination semantics (loop fuel q (PlayerSpecificPolynomialDivision.run p q).2).right*hr

def run (p q : Data) : Result := loop (trim q).length p (trim q)

theorem run_gcd (p q : Data) : (run p q).gcd=PlayerSpecificPolynomialGCD.run p q :=
  gcd_eq _ _ _

theorem run_identity (p q : Data) :
    semantics (run p q).gcd=semantics p*semantics (run p q).left+semantics q*semantics (run p q).right := by
  simpa only [run,trim_semantics] using identity (trim q).length p (trim q)

theorem common_divisors (p q : Data) (r : Polynomial ℚ) :
    r∣semantics (run p q).gcd ↔ r∣semantics p ∧ r∣semantics q := by
  rw [run_gcd]
  exact PlayerSpecificPolynomialGCD.run_common_divisors p q r

end Blotto.PlayerSpecificExtendedGCD
