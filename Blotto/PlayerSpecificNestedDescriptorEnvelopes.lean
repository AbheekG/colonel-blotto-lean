import Blotto.PlayerSpecificPolynomialTerms
import Blotto.PlayerSpecificDescriptorShiftSourceCost
import Blotto.PlayerSpecificDescriptorPadSourceCost
import Blotto.PlayerSpecificDescriptorBinarySourceCost
import Blotto.PlayerSpecificDescriptorSwapSourceCost

/-! Fixed-slot descriptor source work remains polynomial under the nested
assembly's constant slot counts. -/
namespace Blotto.PlayerSpecificNestedDescriptorEnvelopes
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev E (f : ℕ → ℕ) := NaturalPolynomialEnvelope (fun H : ℕ => H) f
private abbrev c := PlayerSpecificPolynomialTerms.constant
private abbrev h := PlayerSpecificPolynomialTerms.input
private theorem add {f g : ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun H => f H+g H) := NaturalPolynomialEnvelope.add hf hg
private theorem mul {f g : ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun H => f H*g H) := NaturalPolynomialEnvelope.mul hf hg
private theorem pow {f : ℕ → ℕ} (hf : E f) (k : ℕ) :
    E (fun H => f H^k) := NaturalPolynomialEnvelope.pow hf k

theorem shift_nine : E (fun H => PlayerSpecificDescriptorShiftSourceCost.work H 9) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 18 3
    (2*9*PlayerSpecificDescriptorShiftRowSourceCost.coefficient)
  have h2 : E (fun H => PlayerSpecificDescriptorCopySourceCost.coefficient*(H+9+5)^5) :=
    mul (c _) (pow (add (add h (c 9)) (c 5)) 5)
  have h3 : E (fun H => PlayerSpecificDescriptorCopySourceCost.coefficient*(step H+9+5)^5) :=
    mul (c _) (pow (add (add (PlayerSpecificSourcePolynomialAutomation.step_envelope h) (c 9)) (c 5)) 5)
  have hall := add (add (add h1 h2) h3) (c 6)
  simpa only [PlayerSpecificDescriptorShiftSourceCost.work,iterate] using hall

theorem pad_three_nine_nine :
    E (fun H => PlayerSpecificDescriptorPadSourceCost.work H 3 9 9) := by
  have h1 : E (fun H => PlayerSpecificDescriptorCopySourceCost.coefficient*(H+3+9+1)^5) :=
    mul (c _) (pow (add (add (add h (c 3)) (c 9)) (c 1)) 5)
  have h2 : E (fun H => PlayerSpecificDescriptorCopySourceCost.coefficient*(H+3+(9+9)+1)^5) :=
    mul (c _) (pow (add (add (add h (c 3)) (c (9+9))) (c 1)) 5)
  have hall := add (add h1 h2) (c (2*(9+1)+6))
  simpa only [PlayerSpecificDescriptorPadSourceCost.work] using hall

theorem pad_fixed (N k m : ℕ) :
    E (fun H => PlayerSpecificDescriptorPadSourceCost.work H N k m) := by
  have h1 : E (fun H => PlayerSpecificDescriptorCopySourceCost.coefficient*(H+N+k+1)^5) :=
    mul (c _) (pow (add (add (add h (c N)) (c k)) (c 1)) 5)
  have h2 : E (fun H => PlayerSpecificDescriptorCopySourceCost.coefficient*(H+N+(k+m)+1)^5) :=
    mul (c _) (pow (add (add (add h (c N)) (c (k+m))) (c 1)) 5)
  have hall := add (add h1 h2) (c (2*(k+1)+6))
  simpa only [PlayerSpecificDescriptorPadSourceCost.work] using hall

theorem swap_eighteen :
    E (fun H => PlayerSpecificDescriptorSwapSourceCost.work H 18) := by
  have h1 : E (fun H => PlayerSpecificDescriptorCopySourceCost.coefficient*(H+18+4)^5) :=
    mul (c _) (pow (add (add h (c 18)) (c 4)) 5)
  have hall := add (add h1 h1) (c 7)
  simpa only [PlayerSpecificDescriptorSwapSourceCost.work] using hall

theorem binary_three_nine_nine :
    E (fun H => PlayerSpecificDescriptorBinarySourceCost.work H 3 9 9) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 13 3
    PlayerSpecificMixtureScalarSourceCost.complementCoefficient
  have h2 : E (fun H => 9*(PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(H+14)^3)) :=
    mul (c 9) (PlayerSpecificPolynomialTerms.iterated 0 14 3
      PlayerSpecificMixtureScalarSourceCost.scaleCoefficient)
  have h3 : E (fun H => 9*(PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 2 H+14)^3)) :=
    mul (c 9) (PlayerSpecificPolynomialTerms.iterated 2 14 3
      PlayerSpecificMixtureScalarSourceCost.scaleCoefficient)
  have h4 : E (fun H => PlayerSpecificDescriptorCopySourceCost.coefficient*(H+3+9+2)^5) :=
    mul (c _) (pow (add (add (add h (c 3)) (c 9)) (c 2)) 5)
  have h5 : E (fun H => PlayerSpecificDescriptorCopySourceCost.coefficient*(H+3+9+2)^5) := h4
  have hi : E (fun H => iterate 3 H) :=
    PlayerSpecificSourcePolynomialAutomation.iterate_envelope h 3
  have hi3 : E (fun H => iterate 3 H+3) := add hi (c 3)
  have hi39 : E (fun H => iterate 3 H+3+(9+9)) := add hi3 (c (9+9))
  have hi392 : E (fun H => iterate 3 H+3+(9+9)+2) := add hi39 (c 2)
  have h6 : E (fun H => PlayerSpecificDescriptorCopySourceCost.coefficient*(iterate 3 H+3+(9+9)+2)^5) :=
    mul (c _) (pow hi392 5)
  have hall := add (add (add (add (add (add h1 h2) h3) h4) h5) h6) (c 6)
  simpa only [PlayerSpecificDescriptorBinarySourceCost.work,iterate] using hall

end Blotto.PlayerSpecificNestedDescriptorEnvelopes
