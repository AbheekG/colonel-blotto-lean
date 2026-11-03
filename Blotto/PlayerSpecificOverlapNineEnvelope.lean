import Blotto.PlayerSpecificPolynomialTerms
import Blotto.PlayerSpecificOverlapTableSourceCost

/-! The fixed nine-by-nine cached overlap table has polynomial source
work in its reached algebraic row height. -/
namespace Blotto.PlayerSpecificOverlapNineEnvelope
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

private abbrev E (f : ℕ → ℕ) := NaturalPolynomialEnvelope (fun H : ℕ => H) f
private abbrev c := PlayerSpecificPolynomialTerms.constant
private abbrev inp := PlayerSpecificPolynomialTerms.input
private theorem add {f g : ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun H => f H+g H) := NaturalPolynomialEnvelope.add hf hg
private theorem mul {f g : ℕ → ℕ} (hf : E f) (hg : E g) :
    E (fun H => f H*g H) := NaturalPolynomialEnvelope.mul hf hg
private theorem pow {f : ℕ → ℕ} (hf : E f) (k : ℕ) :
    E (fun H => f H^k) := NaturalPolynomialEnvelope.pow hf k

theorem cached_row : E (fun H => PlayerSpecificCachedOverlapRowSourceCost.work H) := by
  have h1 := PlayerSpecificPolynomialTerms.iterated 0 28 3
    PlayerSpecificCachedOverlapRowSourceCost.weightCoefficient
  have h2 := PlayerSpecificPolynomialTerms.iterated 0 1 3
    (8000000000*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have h3 := PlayerSpecificPolynomialTerms.iterated 8 1 3
    PlayerSpecificCompareSourceCost.coefficient
  have h4 := PlayerSpecificPolynomialTerms.iterated 0 31 3
    PlayerSpecificCachedOverlapRowSourceCost.pointCoefficient
  have h5 := PlayerSpecificPolynomialTerms.iterated 10 21 3
    (5200*PlayerSpecificResourceCostProfile.rationalCoefficient)
  have hall := add (add (add (add (add h1 h2) h3) h4) h5) (c 10)
  simpa only [PlayerSpecificCachedOverlapRowSourceCost.work,iterate] using hall

theorem overlap_entry : E (fun H => PlayerSpecificOverlapEntrySourceCost.work H 9 9) := by
  have h1 : E (fun H => PlayerSpecificOverlapIndexSourceCost.work 9 9) :=
    c (PlayerSpecificOverlapIndexSourceCost.work 9 9)
  have hbase := add (add (add inp (c 9)) (c 9)) (c 21)
  have h2 : E (fun H => PlayerSpecificOverlapEnvironmentSourceCost.work H 9 9) := by
    have h := mul (c PlayerSpecificOverlapEnvironmentSourceCost.coefficient) (pow hbase 3)
    simpa only [PlayerSpecificOverlapEnvironmentSourceCost.work] using h
  have hall := add (add (add h1 h2) cached_row) (c 2)
  simpa only [PlayerSpecificOverlapEntrySourceCost.work] using hall

theorem overlap_table : E (fun H => PlayerSpecificOverlapTableSourceCost.work H 9 9) := by
  have hc : E (fun H => PlayerSpecificOverlapTableSourceCost.countWork 9 9) :=
    c (PlayerSpecificOverlapTableSourceCost.countWork 9 9)
  have he := mul (c (9*9)) overlap_entry
  have hcopy1 : E (fun H => PlayerSpecificDescriptorCopySourceCost.coefficient*(H+9+6)^5) :=
    mul (c _) (pow (add (add inp (c 9)) (c 6)) 5)
  have hi := PlayerSpecificSourcePolynomialAutomation.iterate_envelope inp 10
  have hcopy2 : E (fun H => PlayerSpecificDescriptorCopySourceCost.coefficient*(iterate 10 H+9*9+7)^5) :=
    mul (c _) (pow (add (add hi (c (9*9))) (c 7)) 5)
  have hall := add (add (add (add (add hc he) hcopy1) hcopy1) hcopy2) (c 6)
  simpa only [PlayerSpecificOverlapTableSourceCost.work] using hall

end Blotto.PlayerSpecificOverlapNineEnvelope
