import Blotto.PlayerSpecificDivisionContract

/-! Actual Euclidean GCD with traced divisions, controls and result copies.
The numerical return refines the immutable checked GCD, so its common-
divisor guarantee applies to the original rational input. -/
namespace Blotto.PlayerSpecificGCDExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

def header (fuel : ℕ) (p q : Data) : Trace :=
  copyRow p++copyRow q++[.control fuel,.control p.length,.control q.length]

def loop : ℕ → Data → Data → Data×Trace
  | 0,p,q =>
    let result := PlayerSpecificDenseExecution.trim p
    (result.1,header 0 p q++result.2++[.control 0])
  | fuel+1,p,q =>
    let pre := header (fuel+1) p q
    if q=[] then
      let result := PlayerSpecificDenseExecution.trim p
      (result.1,pre++result.2++[.control 0]) else
      let divided := PlayerSpecificDivisionExecution.run p q
      let rest := loop fuel q divided.1.2
      (rest.1,pre++divided.2++rest.2++copyRow rest.1++[.control 1])

theorem loop_value (fuel : ℕ) (p q : Data) : (loop fuel p q).1=PlayerSpecificPolynomialGCD.loop fuel p q := by
  induction fuel generalizing p q with
  | zero => simp only [loop,PlayerSpecificDenseExecution.trim_value,PlayerSpecificPolynomialGCD.loop]
  | succ fuel ih =>
    rw [loop,PlayerSpecificPolynomialGCD.loop]
    split
    · exact PlayerSpecificDenseExecution.trim_value p
    · simp only [ih,PlayerSpecificDivisionExecution.value]

def run (p q : Data) : Data×Trace :=
  let divisor := PlayerSpecificDenseExecution.trim q
  let result := loop divisor.1.length p divisor.1
  (result.1,divisor.2++result.2++[.control divisor.1.length])

theorem value (p q : Data) : (run p q).1=PlayerSpecificPolynomialGCD.run p q := by
  simp only [run,loop_value,PlayerSpecificDenseExecution.trim_value,PlayerSpecificPolynomialGCD.run]

theorem loop_bounds (fuel : ℕ) (p q : Data) (H : ℕ) (hp : HasHeight p H) (hq : HasHeight q H)
    (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) (hcap : fuel≤4) :
    HasHeight (loop fuel p q).1 (PlayerSpecificExtendedGCDHeights.linearConstant*(H+1)) ∧ (loop fuel p q).1.length≤4 := by
  have h := PlayerSpecificExtendedGCDHeights.loop_bounds fuel p q H hp hq hH hpl hql
  have hf := PlayerSpecificExtendedGCDHeights.fuel_mono H hcap
  have he := PlayerSpecificExtendedGCDHeights.fixed_degree_linear H
  have hh := mono h.1 (hf.trans he)
  rw [PlayerSpecificExtendedGCD.gcd_eq] at hh
  have hl := h.2.2.2.1
  rw [PlayerSpecificExtendedGCD.gcd_eq] at hl
  rw [loop_value]
  exact ⟨hh,hl⟩

theorem normalized (p q : Data) : Normalized (run p q).1 := by
  rw [value]
  exact PlayerSpecificPolynomialGCD.run_normalized p q

theorem common_divisors (p q : Data) (r : Polynomial ℚ) :
    r∣semantics (run p q).1 ↔ r∣semantics p ∧ r∣semantics q := by
  rw [value]
  exact PlayerSpecificPolynomialGCD.run_common_divisors p q r

end Blotto.PlayerSpecificGCDExecution
