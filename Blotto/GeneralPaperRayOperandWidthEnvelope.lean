import Blotto.GeneralPaperRayEndpointSize

/-! The uniform native ray root width is bounded by the paper's logarithmic
operand envelope. Auxiliary size comes from the constructed classifier;
the bound has no dependence on prior roots or the number of refinements.
-/
namespace Blotto.GeneralPaperRayOperandWidthEnvelope
open GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem word_add (a b : ℕ) : binaryWordWidth (a+b)≤binaryWordWidth a+binaryWordWidth b+1 := by
  have ha := (lt_pow_binaryWordWidth a).trans_le
    (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show binaryWordWidth a≤binaryWordWidth a+binaryWordWidth b by omega))
  have hb := (lt_pow_binaryWordWidth b).trans_le
    (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show binaryWordWidth b≤binaryWordWidth a+binaryWordWidth b by omega))
  have hh : a+b<2^(binaryWordWidth a+binaryWordWidth b+1) := by
    rw [pow_succ]
    omega
  exact binaryWordWidth_le_of_lt_pow (by omega) hh

theorem double_one (a : ℕ) : binaryWordWidth (a+a+1)≤2*binaryWordWidth a+3 := by
  have h1 := word_add a a
  have h2 := word_add (a+a) 1
  have hOne : binaryWordWidth 1=1 := by decide
  omega

theorem auxiliary_width (m k : ℕ) :
    binaryWordWidth (GeneralPaperSourceBasisGridSize.auxiliaryBound m k)≤16+2*binaryWordWidth m+5*binaryWordWidth (prepare m k).H := by
  have h1 := binaryWordWidth_mul 4 m
  have h2 := binaryWordWidth_mul (4*m) (prepare m k).H
  have h3 := binaryWordWidth_mul (4*m*(prepare m k).H) (prepare m k).qbar
  have h4 := binaryWordWidth_mul (4*m*(prepare m k).H*(prepare m k).qbar) (prepare m k).qbar
  have h5 := word_add (4*m*(prepare m k).H*(prepare m k).qbar*(prepare m k).qbar) m
  have hFour : binaryWordWidth 4=3 := by decide
  have hQ := GeneralPaperProxyWidths.cap_width m k
  unfold GeneralPaperSourceBasisGridSize.auxiliaryBound
  omega

theorem stage_width (m k j N determinant P : ℕ) (hD : determinant≤(prepare m k).H)
    (hP : P≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k) :
    GeneralPaperRayUniformSize.width (N*determinant) determinant m 1 (j*(prepare m k).H*(m+1)+1) P≤
      64+binaryWordWidth N+14*binaryWordWidth (prepare m k).H+10*binaryWordWidth m+2*binaryWordWidth j := by
  let A := GeneralPaperRayUniformSize.interceptCap m 1 P
  let W := j*(prepare m k).H*(m+1)+1
  let B := GeneralPaperRayUniformSize.slopeCap m W
  have hOne : binaryWordWidth 1=1 := by decide
  have hTwo : binaryWordWidth 2=2 := by decide
  have hM := word_add m 1
  have hP' := (binaryWordWidth_mono hP).trans (auxiliary_width m k)
  have hD' := binaryWordWidth_mono hD
  have hND := binaryWordWidth_mul N determinant
  have hA : binaryWordWidth A≤binaryWordWidth m+binaryWordWidth P+5 := by
    have h1 := binaryWordWidth_mul (m+1) (P+2)
    have h2 := word_add P 2
    change binaryWordWidth ((m+1)*(1+P+1))≤_
    have he : 1+P+1=P+2 := by omega
    rw [he]
    omega
  have hW : binaryWordWidth W≤binaryWordWidth j+binaryWordWidth (prepare m k).H+binaryWordWidth m+4 := by
    have h1 := binaryWordWidth_mul j (prepare m k).H
    have h2 := binaryWordWidth_mul (j*(prepare m k).H) (m+1)
    have h3 := word_add (j*(prepare m k).H*(m+1)) 1
    change binaryWordWidth (j*(prepare m k).H*(m+1)+1)≤_
    omega
  have hB : binaryWordWidth B≤binaryWordWidth m+binaryWordWidth W+4 := by
    have h1 := binaryWordWidth_mul (m+1) (W+1)
    have h2 := word_add W 1
    change binaryWordWidth ((m+1)*(W+1))≤_
    omega
  have hAA := double_one A
  have hBB := double_one B
  change binaryWordWidth (A+A+1)+binaryWordWidth (N*determinant)+binaryWordWidth (B+B+1)+binaryWordWidth determinant≤_
  omega

theorem paper_envelope (m k j N determinant P S T : ℕ) (hj : j≤m*((prepare m k).K-1))
    (hD : determinant≤(prepare m k).H) (hP : P≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k) :
    GeneralPaperRayUniformSize.width (N*determinant) determinant m 1 (j*(prepare m k).H*(m+1)+1) P≤
      78+binaryWordWidth N+14*((prepare m k).d+2)*binaryWordWidth (m+3)+
        12*binaryWordWidth ((prepare m k).d+m+(prepare m k).K+S+T+2) := by
  have hs := stage_width m k j N determinant P hD hP
  have hh := GeneralPaperProxyWidths.H_width m k
  have hj' : j≤(prepare m k).d := by rw [(data m k).2.2.1]; exact hj
  have hmW := binaryWordWidth_mono (show m≤(prepare m k).d+m+(prepare m k).K+S+T+2 by omega)
  have hjW := binaryWordWidth_mono (show j≤(prepare m k).d+m+(prepare m k).K+S+T+2 by omega)
  nlinarith only [hs,hh,hmW,hjW]

end Blotto.GeneralPaperRayOperandWidthEnvelope
