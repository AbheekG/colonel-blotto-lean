import Blotto.GeneralPaperBasisPreparationBits

/-! Fresh-preparation prices have logarithmic raw operand envelopes.
Dimension and input magnitudes enter as word lengths; no solve/iteration
history or cancellation assumption appears in the paper envelope.
-/
namespace Blotto.GeneralPaperBasisPreparationWidths
open GeneralPaperRayOperandWidthEnvelope GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 7000000

theorem rhs_bound_width (d C N B : ℕ) : binaryWordWidth (GeneralPaperBasisRHSBits.bound d C N B+1)≤
    8*(binaryWordWidth (d+1)+binaryWordWidth (C+1)+binaryWordWidth (N+1)+binaryWordWidth (B+1)+1) := by
  have h1 := word_add N B
  have h2 := word_add (N+B) (d*N)
  have h3 := binaryWordWidth_mul d N
  have h4 : binaryWordWidth (GeneralPaperBasisRHSBits.bound d C N B)≤binaryWordWidth C+binaryWordWidth (N+B+d*N) := binaryWordWidth_mul _ _
  have h5 := word_add (GeneralPaperBasisRHSBits.bound d C N B) 1
  have hd : binaryWordWidth d≤binaryWordWidth (d+1) := binaryWordWidth_mono (by omega)
  have hc : binaryWordWidth C≤binaryWordWidth (C+1) := binaryWordWidth_mono (by omega)
  have hn : binaryWordWidth N≤binaryWordWidth (N+1) := binaryWordWidth_mono (by omega)
  have hb : binaryWordWidth B≤binaryWordWidth (B+1) := binaryWordWidth_mono (by omega)
  have ho : binaryWordWidth 1=1 := by decide
  omega

theorem rhs_width (d C N B : ℕ) : GeneralPaperBasisRHSBits.width d C N B≤
    16*(binaryWordWidth (d+1)+binaryWordWidth (C+1)+binaryWordWidth (N+1)+binaryWordWidth (B+1)+1) := by
  have h1 := word_add N B
  have h2 := word_add (N+B) (d*N)
  have h3 := binaryWordWidth_mul d N
  have h4 : binaryWordWidth (GeneralPaperBasisRHSBits.bound d C N B)≤binaryWordWidth C+binaryWordWidth (N+B+d*N) := binaryWordWidth_mul _ _
  have h5 := word_add C N
  have h6 := word_add (C+N) B
  have h7 := word_add (C+N+B) (GeneralPaperBasisRHSBits.bound d C N B)
  have h8 := word_add (C+N+B+GeneralPaperBasisRHSBits.bound d C N B) 1
  have hCap := GeneralPaperIntegerDotPrice.cap_width d C N
  have hd : binaryWordWidth d≤binaryWordWidth (d+1) := binaryWordWidth_mono (by omega)
  have hc : binaryWordWidth C≤binaryWordWidth (C+1) := binaryWordWidth_mono (by omega)
  have hn : binaryWordWidth N≤binaryWordWidth (N+1) := binaryWordWidth_mono (by omega)
  have hb : binaryWordWidth B≤binaryWordWidth (B+1) := binaryWordWidth_mono (by omega)
  have ho : binaryWordWidth 1=1 := by decide
  unfold GeneralPaperBasisRHSBits.width GeneralPaperBasisRHSBits.coreCap
  omega

theorem point_width (j d C N H B : ℕ) : GeneralPaperBasisPreparationBits.pointWidth j d C N H B≤
    256*(binaryWordWidth (j+1)+binaryWordWidth (d+1)+binaryWordWidth (C+1)+binaryWordWidth (N+1)+
      binaryWordWidth (H+1)+binaryWordWidth (B+1)+1) := by
  have hr := rhs_width d C N B
  have hb := rhs_bound_width d C N B
  have hs := GeneralPaperBasisSolveBits.width_bound j N H (GeneralPaperBasisRHSBits.bound d C N B)
  have hn : binaryWordWidth N≤binaryWordWidth (N+1) := binaryWordWidth_mono (by omega)
  unfold GeneralPaperBasisPreparationBits.pointWidth
  omega

def envelope (d C N H B : ℕ) : ℕ := 512*(binaryWordWidth (d+1)+binaryWordWidth (C+1)+binaryWordWidth (N+1)+
  binaryWordWidth (H+1)+binaryWordWidth (B+1)+1)

theorem component_widths (j d C N H B : ℕ) (hj : j≤d) :
    GeneralPaperBasisPreparationBits.pointWidth j d C N H B≤envelope d C N H B ∧
    GeneralPaperBasisSolveBits.width j 1 H C≤envelope d C N H B := by
  have hp := point_width j d C N H B
  have hd := GeneralPaperBasisSolveBits.width_bound j 1 H C
  have hjw : binaryWordWidth (j+1)≤binaryWordWidth (d+1) := binaryWordWidth_mono (by omega)
  have hTwo : binaryWordWidth (1+1)=2 := by decide
  unfold envelope
  omega

theorem paper_envelope (m k N S T : ℕ) :
    envelope (m*((prepare m k).K-1)) (m+1) N (prepare m k).H (GeneralPaperSourceBasisGridSize.auxiliaryBound m k)≤
      16384+512*binaryWordWidth N+3072*((prepare m k).d+2)*binaryWordWidth (m+3)+
        2048*binaryWordWidth ((prepare m k).d+m+(prepare m k).K+S+T+2) := by
  have hN := word_add N 1
  have hH := word_add (prepare m k).H 1
  have hB := word_add (GeneralPaperSourceBasisGridSize.auxiliaryBound m k) 1
  have hAux := auxiliary_width m k
  have hHP := GeneralPaperProxyWidths.H_width m k
  have hOne : binaryWordWidth 1=1 := by decide
  have hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤binaryWordWidth ((prepare m k).d+m+(prepare m k).K+S+T+2) := by
    apply binaryWordWidth_mono
    rw [←(GeneralPaperProxyParameters.data m k).2.2.1]
    omega
  have hM := binaryWordWidth_mono (show m+2≤(prepare m k).d+m+(prepare m k).K+S+T+2 by omega)
  have hM0 := binaryWordWidth_mono (show m≤(prepare m k).d+m+(prepare m k).K+S+T+2 by omega)
  unfold envelope
  have he : (m+1)+1=m+2 := by omega
  rw [he]
  nlinarith only [hN,hH,hB,hAux,hHP,hOne,hDim,hM,hM0]

end Blotto.GeneralPaperBasisPreparationWidths
