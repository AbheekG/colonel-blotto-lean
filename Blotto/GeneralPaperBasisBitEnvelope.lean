import Blotto.GeneralPaperBasisBudgetBits

/-! One logarithmic paper operand envelope controls every native basis
stage phase. Index capacities for reached arrays remain explicit, as do
the separate global source reference/score/control-capacity obligations.
-/
namespace Blotto.GeneralPaperBasisBitEnvelope
open GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 8000000

def width (m k N S T : ℕ) : ℕ := 16384+512*binaryWordWidth N+3072*((prepare m k).d+2)*binaryWordWidth (m+3)+
  2048*binaryWordWidth ((prepare m k).d+m+(prepare m k).K+S+T+2)

theorem labels_two (m k : ℕ) : 2≤(prepare m k).K := by
  rw [(GeneralPaperProxyParameters.data m k).1,GeneralPaperScoreScaleParameters.label_power]
  exact Nat.one_lt_pow (by omega : 7+k≠0) (by decide : 1<(2:ℕ))

theorem dimension_bounds (m k : ℕ) (hm : 0<m) : m≤m*((prepare m k).K-1) ∧ (prepare m k).K+1≤m*((prepare m k).K-1)+3 := by
  have hk := labels_two m k
  have h1 : m≤m*((prepare m k).K-1) := by nlinarith only [show 1≤(prepare m k).K-1 by omega]
  have h2 : (prepare m k).K-1≤m*((prepare m k).K-1) := by nlinarith only [show 1≤m by omega]
  exact ⟨h1,by omega⟩

theorem index_capacities (m k W : ℕ) (hm : 0<m) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W) :
    binaryWordWidth (m*((prepare m k).K-1)+1)≤W ∧ binaryWordWidth ((prepare m k).K+1)≤W ∧ binaryWordWidth (m+1)≤W := by
  have hb := dimension_bounds m k hm
  exact ⟨(binaryWordWidth_mono (by omega : m*((prepare m k).K-1)+1≤m*((prepare m k).K-1)+3)).trans hDim,
    (binaryWordWidth_mono hb.2).trans hDim,(binaryWordWidth_mono (by omega : m+1≤m*((prepare m k).K-1)+3)).trans hDim⟩

theorem components (m k j N S T : ℕ) (hj : j≤m*((prepare m k).K-1)) :
    GeneralPaperBasisPreparationWidths.envelope (m*((prepare m k).K-1)) (m+1) N (prepare m k).H (GeneralPaperSourceBasisGridSize.auxiliaryBound m k)≤width m k N S T ∧
    GeneralPaperBasisAdvanceBits.width j (m*((prepare m k).K-1)) m (prepare m k).H≤width m k N S T ∧
    GeneralPaperBasisBudgetBits.width N (GeneralPaperSourceBasisGridSize.auxiliaryBound m k)≤width m k N S T := by
  have hp := GeneralPaperBasisPreparationWidths.paper_envelope m k N S T
  have hc := GeneralPaperBasisCacheStageBits.paper_width m k j S T hj
  have hD : binaryWordWidth (m*((prepare m k).K-1)+1)≤binaryWordWidth ((prepare m k).d+m+(prepare m k).K+S+T+2) := by
    apply binaryWordWidth_mono
    rw [←(GeneralPaperProxyParameters.data m k).2.2.1]
    omega
  have hM := binaryWordWidth_mono (show m+1≤(prepare m k).d+m+(prepare m k).K+S+T+2 by omega)
  have hM0 := binaryWordWidth_mono (show m≤(prepare m k).d+m+(prepare m k).K+S+T+2 by omega)
  have hB := GeneralPaperRayOperandWidthEnvelope.auxiliary_width m k
  have hH := GeneralPaperProxyWidths.H_width m k
  refine ⟨hp,?_,?_⟩
  · unfold GeneralPaperBasisAdvanceBits.width width
    nlinarith only [hc,hD,hM,Nat.zero_le (binaryWordWidth N)]
  · unfold GeneralPaperBasisBudgetBits.width width
    nlinarith only [hB,hH,hM0]

theorem ray_width (m k j N determinant P S T : ℕ) (hj : j≤m*((prepare m k).K-1))
    (hD : determinant≤(prepare m k).H) (hP : P≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k) :
    6*GeneralPaperRayUniformSize.width (N*determinant) determinant m 1 (j*(prepare m k).H*(m+1)+1) P+9≤width m k N S T := by
  have hh := GeneralPaperRayOperandWidthEnvelope.paper_envelope m k j N determinant P S T hj hD hP
  unfold width
  nlinarith only [hh,Nat.zero_le (binaryWordWidth N)]

theorem advance_scale (j d m W P : ℕ) (hj : j≤d) (hm : m≤d) :
    8192*((j+2)^2+d+m+j+3)*(W+P)≤65536*(d+1)^2*(W+P) := by
  have hSq : (j+2)^2≤(d+2)^2 := by nlinarith only [hj]
  have hh : 8192*((j+2)^2+d+m+j+3)≤65536*(d+1)^2 := by nlinarith only [hSq,hj,hm]
  exact Nat.mul_le_mul_right (W+P) hh

theorem endpoint_profile_mono (T m K S W P Q : ℕ) (hPQ : P≤Q) :
    GeneralPaperEndpointPriceControl.profile T m K S W P≤GeneralPaperEndpointPriceControl.profile T m K S W Q := by
  unfold GeneralPaperEndpointPriceControl.profile GeneralPaperHighSearchPriceFacts.profile GeneralPaperHighSearchPriceControl.profile
    GeneralPaperParametricPriceProfiles.profile GeneralPaperParametricRecursionPrice.profile GeneralPaperParametricStageBits.profile
    GeneralPaperAffineStepPrice.profile GeneralPaperFinalRefinementPrice.profile GeneralPaperFinalRefinementPrice.envelope
    GeneralPaperHighBlockerPrice.profile GeneralPaperFixedViolationPrice.profile
  gcongr

end Blotto.GeneralPaperBasisBitEnvelope
