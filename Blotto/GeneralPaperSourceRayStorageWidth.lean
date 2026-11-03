import Blotto.GeneralPaperRayQueryStorageEnvelope
import Blotto.GeneralPaperSourceRayOperandSize

/-! A source-wide, short-unit operand envelope for ray-query storage.
The actual classifier grid, original-basis determinant and auxiliary bound
control all roots and their midpoint probes. Prior root denominators and
original exact budget input height do not enter this envelope. -/
namespace Blotto.GeneralPaperSourceRayStorageWidth
open GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 2600000

def gridWord (m k : ℕ) : ℕ := 3+binaryWordWidth m+binaryWordWidth (prepare m k).H+2*binaryWordWidth (prepare m k).qbar

def rootWidth (m k : ℕ) : ℕ :=
  78+gridWord m k+14*((prepare m k).d+2)*binaryWordWidth (m+3)+
    12*binaryWordWidth ((prepare m k).d+m+(prepare m k).K+(prepare m k).S+
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+2)

def width (m k : ℕ) : ℕ := 7+6*rootWidth m k

theorem root_positive (m k : ℕ) : 0<rootWidth m k := by unfold rootWidth; omega

theorem grid_bound (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    binaryWordWidth (GeneralPaperInitializerSelectedControls.controls m k b reciprocal).N≤gridWord m k :=
  GeneralPaperInitializerSelectedControls.N_width m k b hb reciprocal

theorem root_bound (m k j : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (determinant P : ℕ)
    (hj : j≤m*((prepare m k).K-1)) (hD : determinant≤(prepare m k).H)
    (hP : P≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k) :
    GeneralPaperRayUniformSize.width
      ((GeneralPaperInitializerSelectedControls.controls m k b reciprocal).N*determinant) determinant
      m 1 (j*(prepare m k).H*(m+1)+1) P≤rootWidth m k := by
  have hr := GeneralPaperRayOperandWidthEnvelope.paper_envelope m k j
    (GeneralPaperInitializerSelectedControls.controls m k b reciprocal).N determinant P (prepare m k).S
    (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows hj hD hP
  have hg := grid_bound m k b hb reciprocal
  unfold rootWidth
  omega

theorem probe_word (m k j : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (determinant P : ℕ)
    (hj : j≤m*((prepare m k).K-1)) (hD : determinant≤(prepare m k).H)
    (hP : P≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k) (t : ℚ)
    (hT : RationalHeight t (2*rootWidth m k+3)) :
    GeneralPaperCommonLatticeDPBits.width
      ((GeneralPaperInitializerSelectedControls.controls m k b reciprocal).N*determinant*t.den)
      (1+(j*(prepare m k).H*(m+1)+1)+1) m≤width m k := by
  have hRoot := root_bound m k j b hb reciprocal determinant P hj hD hP
  have hWord := GeneralPaperRayQueryWidth.width (m:=m)
    (D:=(GeneralPaperInitializerSelectedControls.controls m k b reciprocal).N*determinant)
    (E:=determinant) (X:=1) (V:=j*(prepare m k).H*(m+1)+1) (P:=P) t hT
  unfold width
  omega

end Blotto.GeneralPaperSourceRayStorageWidth
