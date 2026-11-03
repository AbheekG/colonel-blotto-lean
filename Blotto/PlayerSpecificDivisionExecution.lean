import Blotto.PlayerSpecificMonicDivisionTraceCost

/-! Actual arbitrary rational polynomial division with traced normalization,
monic recursion and cached inverse-leading quotient rescaling. -/
namespace Blotto.PlayerSpecificDivisionExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run (p q : Data) : (Data×Data)×Trace :=
  let divisor := PlayerSpecificDenseExecution.trim q
  let pre := divisor.2++copyRow p++[.control p.length,.control divisor.1.length]
  if divisor.1=[] then
    let remainder := PlayerSpecificDenseExecution.trim p
    (([],remainder.1),pre++remainder.2++copyRow []++[.control 0]) else
    let normalized := PlayerSpecificMonicizeExecution.run divisor.1
    let divided := PlayerSpecificMonicDivisionExecution.run normalized.1.2 p.length p
    let scaled := PlayerSpecificDenseExecution.scale normalized.1.1 divided.1.1
    let quotient := PlayerSpecificDenseExecution.trim scaled.1
    ((quotient.1,divided.1.2),pre++normalized.2++divided.2++scaled.2++quotient.2++copyRow divided.1.2++[.control 1])

theorem value (p q : Data) : (run p q).1=PlayerSpecificPolynomialDivision.run p q := by
  rw [run,PlayerSpecificPolynomialDivision.run]
  simp only [PlayerSpecificDenseExecution.trim_value]
  split
  · rfl
  · simp only [PlayerSpecificDenseExecution.scale_value,PlayerSpecificMonicizeExecution.inverse_value,
      PlayerSpecificMonicizeExecution.polynomial_value,PlayerSpecificMonicDivisionExecution.value,PlayerSpecificMonicDivision.run]

theorem heights (p q : Data) (H : ℕ) (hp : HasHeight p H) (hq : HasHeight q H)
    (hH : 1≤H) (hpl : p.length≤4) (hql : q.length≤4) :
    HasHeight (run p q).1.1 (32211*H+9666) ∧ HasHeight (run p q).1.2 (32211*H+9666) := by
  rw [value]
  have h := PlayerSpecificDivisionHeights.run_height p q H hp hq hH hpl hql
  rw [PlayerSpecificDivisionHeights.linear] at h
  exact h

theorem lengths (p q : Data) : (run p q).1.1.length≤p.length ∧ (run p q).1.2.length≤p.length := by
  rw [value]
  exact ⟨PlayerSpecificDivisionHeights.quotient_length p q,PlayerSpecificDivisionHeights.remainder_length p q⟩

theorem normalized (p q : Data) : Normalized (run p q).1.1 ∧ Normalized (run p q).1.2 := by
  rw [value]
  exact ⟨PlayerSpecificPolynomialDivision.quotient_normalized p q,PlayerSpecificPolynomialDivision.remainder_normalized p q⟩

theorem refines (p q : Data) :
    semantics p/semantics q=semantics (run p q).1.1 ∧ semantics p%semantics q=semantics (run p q).1.2 := by
  rw [value]
  exact PlayerSpecificPolynomialDivision.refines p q

end Blotto.PlayerSpecificDivisionExecution
