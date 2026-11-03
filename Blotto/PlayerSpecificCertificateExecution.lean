import Blotto.PlayerSpecificHeadInverseExecution

/-! Cached squarefree polynomial and its actual unit right Bezout
certificate. The squarefree input and its derivative are evaluated once. -/
namespace Blotto.PlayerSpecificCertificateExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

def certificate (h : Data) : PlayerSpecificExtendedGCD.Result×Trace :=
  let differentiated := PlayerSpecificDenseExecution.derivative h
  let result := PlayerSpecificExtendedGCDExecution.run h differentiated.1
  (result.1,differentiated.2++result.2++[.control h.length])

theorem certificate_value (h : Data) :
    (certificate h).1=PlayerSpecificExtendedGCD.run h (derivative h) := by
  simp only [certificate,PlayerSpecificExtendedGCDExecution.value,PlayerSpecificDenseExecution.derivative_value]

def normalize (result : PlayerSpecificExtendedGCD.Result) : Data×Trace :=
  let inverted := PlayerSpecificHeadInverseExecution.run result.gcd
  let scaled := PlayerSpecificDenseExecution.scale inverted.1 result.right
  (scaled.1,inverted.2++scaled.2++copyRow scaled.1++[.control result.right.length])

theorem normalize_value (result : PlayerSpecificExtendedGCD.Result) :
    (normalize result).1=scale ((result.gcd.headD 0)⁻¹) result.right := by
  simp only [normalize,PlayerSpecificDenseExecution.scale_value,PlayerSpecificHeadInverseExecution.value]

def run (p : Data) : (Data×Data)×Trace :=
  let squarefree := PlayerSpecificSquarefreeExecution.run p
  let computed := certificate squarefree.1
  let unit := normalize computed.1
  ((squarefree.1,unit.1),squarefree.2++computed.2++unit.2++copyRow squarefree.1++[.control unit.1.length])

theorem polynomial_value (p : Data) : (run p).1.1=PlayerSpecificSquarefreeAlgorithm.run p :=
  PlayerSpecificSquarefreeExecution.value p

theorem unit_value (p : Data) : (run p).1.2=PlayerSpecificSquarefreeCoprime.unitRight p := by
  simp only [run,normalize_value,certificate_value,PlayerSpecificSquarefreeExecution.value,
    PlayerSpecificSquarefreeCoprime.unitRight,PlayerSpecificSquarefreeCoprime.certificate]

theorem bounds (p : Data) (H : ℕ) (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤4) :
    HasHeight (run p).1.1 (PlayerSpecificSquarefreeHeights.quotientHeight H) ∧
      HasHeight (run p).1.2 (2*PlayerSpecificSquarefreeHeights.certificateHeight H) ∧
      (run p).1.1.length≤4 ∧ (run p).1.2.length≤17 := by
  rw [polynomial_value,unit_value]
  have hq := PlayerSpecificSquarefreeHeights.quotient_bounds p H hp hH hlen
  have hu := PlayerSpecificSquarefreeHeights.unitRight_bounds p H hp hH hlen
  exact ⟨hq.1,hu.1,hq.2,hu.2⟩

end Blotto.PlayerSpecificCertificateExecution
