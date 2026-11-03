import Blotto.PlayerSpecificGCDTraceCost

/-! Actual extended Euclid with traced polynomial divisions and coefficient
updates. Numerical returns refine the existing executed Bezout algorithm. -/
namespace Blotto.PlayerSpecificExtendedGCDExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

def copyResult (result : PlayerSpecificExtendedGCD.Result) : Trace :=
  copyRow result.gcd++copyRow result.left++copyRow result.right++
    [.control result.gcd.length,.control result.left.length,.control result.right.length]

def loop : ℕ → Data → Data → PlayerSpecificExtendedGCD.Result×Trace
  | 0,p,q =>
    let current := PlayerSpecificDenseExecution.trim p
    let result : PlayerSpecificExtendedGCD.Result := ⟨current.1,[1],[]⟩
    (result,PlayerSpecificGCDExecution.header 0 p q++current.2++copyResult result++[.control 0])
  | fuel+1,p,q =>
    let pre := PlayerSpecificGCDExecution.header (fuel+1) p q
    if q=[] then
      let current := PlayerSpecificDenseExecution.trim p
      let result : PlayerSpecificExtendedGCD.Result := ⟨current.1,[1],[]⟩
      (result,pre++current.2++copyResult result++[.control 0]) else
      let divided := PlayerSpecificDivisionExecution.run p q
      let rest := loop fuel q divided.1.2
      let product := PlayerSpecificDenseExecution.multiply divided.1.1 rest.1.right
      let difference := PlayerSpecificDenseExecution.subtract rest.1.left product.1
      let normalized := PlayerSpecificDenseExecution.trim difference.1
      let result : PlayerSpecificExtendedGCD.Result := ⟨rest.1.gcd,rest.1.right,normalized.1⟩
      (result,pre++divided.2++rest.2++product.2++difference.2++normalized.2++copyResult result++[.control 1])

theorem loop_value (fuel : ℕ) (p q : Data) : (loop fuel p q).1=PlayerSpecificExtendedGCD.loop fuel p q := by
  induction fuel generalizing p q with
  | zero => simp only [loop,PlayerSpecificDenseExecution.trim_value,PlayerSpecificExtendedGCD.loop]
  | succ fuel ih =>
    rw [loop,PlayerSpecificExtendedGCD.loop]
    split
    · simp only [PlayerSpecificDenseExecution.trim_value]
    · simp only [PlayerSpecificDenseExecution.trim_value,PlayerSpecificDenseExecution.subtract_value,
        PlayerSpecificDenseExecution.multiply_value,PlayerSpecificDivisionExecution.value,ih]

def run (p q : Data) : PlayerSpecificExtendedGCD.Result×Trace :=
  let divisor := PlayerSpecificDenseExecution.trim q
  let result := loop divisor.1.length p divisor.1
  (result.1,divisor.2++result.2++[.control divisor.1.length])

theorem value (p q : Data) : (run p q).1=PlayerSpecificExtendedGCD.run p q := by
  simp only [run,loop_value,PlayerSpecificDenseExecution.trim_value,PlayerSpecificExtendedGCD.run]

theorem loop_bounds (fuel : ℕ) (p q : Data) (H : ℕ) (hp : HasHeight p H) (hq : HasHeight q H)
    (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) (hcap : fuel≤4) :
    HasHeight (loop fuel p q).1.gcd (PlayerSpecificExtendedGCDHeights.linearConstant*(H+1)) ∧
      HasHeight (loop fuel p q).1.left (PlayerSpecificExtendedGCDHeights.linearConstant*(H+1)) ∧
      HasHeight (loop fuel p q).1.right (PlayerSpecificExtendedGCDHeights.linearConstant*(H+1)) ∧
      (loop fuel p q).1.gcd.length≤4 ∧ (loop fuel p q).1.left.length≤17 ∧ (loop fuel p q).1.right.length≤17 := by
  rw [loop_value]
  have h := PlayerSpecificExtendedGCDHeights.loop_bounds fuel p q H hp hq hH hpl hql
  have hf := PlayerSpecificExtendedGCDHeights.fuel_mono H hcap
  have he := PlayerSpecificExtendedGCDHeights.fixed_degree_linear H
  exact ⟨mono h.1 (hf.trans he),mono h.2.1 (hf.trans he),mono h.2.2.1 (hf.trans he),h.2.2.2.1,by omega,by omega⟩

theorem identity (p q : Data) : semantics (run p q).1.gcd=
    semantics p*semantics (run p q).1.left+semantics q*semantics (run p q).1.right := by
  rw [value]
  exact PlayerSpecificExtendedGCD.run_identity p q

theorem run_bounds (p q : Data) (H : ℕ) (hp : HasHeight p H) (hq : HasHeight q H)
    (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) :
    HasHeight (run p q).1.gcd (PlayerSpecificExtendedGCDHeights.linearConstant*(H+1)) ∧
      HasHeight (run p q).1.left (PlayerSpecificExtendedGCDHeights.linearConstant*(H+1)) ∧
      HasHeight (run p q).1.right (PlayerSpecificExtendedGCDHeights.linearConstant*(H+1)) ∧
      (run p q).1.gcd.length≤4 ∧ (run p q).1.left.length≤17 ∧ (run p q).1.right.length≤17 := by
  have hqH : HasHeight (PlayerSpecificDenseExecution.trim q).1 H := by
    rw [PlayerSpecificDenseExecution.trim_value]
    exact trim_height hq
  have hql' : (PlayerSpecificDenseExecution.trim q).1.length≤4 := by
    rw [PlayerSpecificDenseExecution.trim_value]
    exact (trim_length q).trans hql
  exact loop_bounds (PlayerSpecificDenseExecution.trim q).1.length p (PlayerSpecificDenseExecution.trim q).1 H hp hqH hH hpl hql' hql'

theorem common_divisors (p q : Data) (r : Polynomial ℚ) :
    r∣semantics (run p q).1.gcd ↔ r∣semantics p ∧ r∣semantics q := by
  rw [value]
  exact PlayerSpecificExtendedGCD.common_divisors p q r

end Blotto.PlayerSpecificExtendedGCDExecution
