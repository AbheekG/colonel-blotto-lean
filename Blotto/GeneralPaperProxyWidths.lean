import Blotto.GeneralPaperPreparedProxySource
import Blotto.FareySourceUniverses

/-! Constructed root/alphabet word bounds. These bound the actual stored
integer controls without reading an original input encoding. They are size
facts, not a completed fast-bit or abstract live-storage execution ledger.
-/
namespace Blotto.GeneralPaperProxyWidths
open GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem H_width (m k : ℕ) :
    binaryWordWidth (prepare m k).H≤1+((prepare m k).d+2)*binaryWordWidth (m+3) := by
  rw [(data m k).2.2.2.1]
  exact Farey.binaryWordWidth_power _ _

theorem grid_width (m k : ℕ) : binaryWordWidth (prepare m k).Qg≤4+2*binaryWordWidth (prepare m k).H := by
  have hs := binaryWordWidth_mono (grid_upper m k).le
  have h1 := binaryWordWidth_mul (8*(prepare m k).H) (prepare m k).H
  have h2 := binaryWordWidth_mul 8 (prepare m k).H
  have h8 : binaryWordWidth 8=4 := by decide
  omega

theorem cap_width (m k : ℕ) : binaryWordWidth (prepare m k).qbar≤6+2*binaryWordWidth (prepare m k).H := by
  rw [(data m k).2.2.2.2.2.2]
  have h1 := binaryWordWidth_mul 2 (prepare m k).Qg
  have h2 := grid_width m k
  have hTwo : binaryWordWidth 2=2 := by decide
  omega

theorem grid_bits (m k : ℕ) : (prepare m k).gridBits≤3+2*binaryWordWidth (prepare m k).H := by
  have hd := GeneralPaperPowerCeiling.loop_depth (4*(prepare m k).H*(prepare m k).H) 1 (by decide)
  change (GeneralPaperPowerCeiling.ceiling (4*(prepare m k).H*(prepare m k).H)).doublings≤_ at hd
  rw [←(data m k).2.2.2.2.2.1] at hd
  have h1 := binaryWordWidth_mul (4*(prepare m k).H) (prepare m k).H
  have h2 := binaryWordWidth_mul 4 (prepare m k).H
  have h4 : binaryWordWidth 4=3 := by decide
  omega

theorem denominator_width (m k : ℕ) :
    binaryWordWidth (alphabet m k).D≤binaryWordWidth (prepare m k).qbar+1+
      (m*((GeneralPaperComparatorParameters.countRun k).power-1)+1)*binaryWordWidth (m+2) := by
  change binaryWordWidth (GeneralPaperComparatorParameters.prepare m k (prepare m k).qbar).D≤_
  rw [(GeneralPaperComparatorParameters.data m k (prepare m k).qbar).2.2.1]
  have hm := binaryWordWidth_mul (prepare m k).qbar ((m+2)^(m*((GeneralPaperComparatorParameters.countRun k).power-1)+1))
  have hp := Farey.binaryWordWidth_power (m+2) (m*((GeneralPaperComparatorParameters.countRun k).power-1)+1)
  omega

theorem lambda_width (m k : ℕ) : (alphabet m k).lambda≤6+2*binaryWordWidth (alphabet m k).D := by
  let qbar := (prepare m k).qbar
  have hd := GeneralPaperPowerCeiling.loop_depth
    (4*(GeneralPaperComparatorParameters.prepare m k qbar).D*(GeneralPaperComparatorParameters.prepare m k qbar).D) 1 (by decide)
  change (GeneralPaperPowerCeiling.ceiling
    (4*(GeneralPaperComparatorParameters.prepare m k qbar).D*(GeneralPaperComparatorParameters.prepare m k qbar).D)).doublings≤_ at hd
  have h1 := binaryWordWidth_mul (4*(alphabet m k).D) (alphabet m k).D
  have h2 := binaryWordWidth_mul 4 (alphabet m k).D
  have h4 : binaryWordWidth 4=3 := by decide
  change (GeneralPaperComparatorParameters.prepare m k qbar).lambda≤_
  rw [(GeneralPaperComparatorParameters.data m k qbar).2.2.2.2]
  change _≤6+2*binaryWordWidth (GeneralPaperComparatorParameters.prepare m k qbar).D
  change binaryWordWidth (4*(GeneralPaperComparatorParameters.prepare m k qbar).D*(GeneralPaperComparatorParameters.prepare m k qbar).D)≤
    binaryWordWidth (4*(GeneralPaperComparatorParameters.prepare m k qbar).D)+
      binaryWordWidth (GeneralPaperComparatorParameters.prepare m k qbar).D at h1
  change binaryWordWidth (4*(GeneralPaperComparatorParameters.prepare m k qbar).D)≤
    binaryWordWidth 4+binaryWordWidth (GeneralPaperComparatorParameters.prepare m k qbar).D at h2
  omega

theorem lambda_bound (m k : ℕ) :
    (alphabet m k).lambda≤24+4*((prepare m k).d+2)*binaryWordWidth (m+3)+
      2*(m*((GeneralPaperComparatorParameters.countRun k).power-1)+1)*binaryWordWidth (m+2) := by
  have hl := lambda_width m k
  have hd := denominator_width m k
  have hq := cap_width m k
  have hh := H_width m k
  nlinarith only [hl,hd,hq,hh]

end Blotto.GeneralPaperProxyWidths
