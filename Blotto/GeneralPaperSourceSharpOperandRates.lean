import Blotto.GeneralPaperSourceEndpointOwnerRates

/-! The selected source alphabet and short-unit operands have soft degree
(1,0,1). This removes the unnecessary extra Lambda factor in componentwise
rate composition. Actual constructed caps and comparator counts supply the
proof; no algorithm, height oracle or paper computational model changes. -/
namespace Blotto.GeneralPaperSourceSharpOperandRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 8192

@[fun_prop]
theorem comparator_count : Rated (fun x => (GeneralPaperComparatorParameters.countRun x.k).power) 0 0 1 := by
  have he : (fun x : Input => (GeneralPaperComparatorParameters.countRun x.k).power)=(fun x : Input => 2^(17+x.k)) :=
    funext (fun x => GeneralPaperComparatorParameters.count_power x.k)
  rw [he]
  exact dyadic_accuracy 17

@[fun_prop]
theorem cap_word : Rated (fun x => binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).qbar) 1 0 1 := by
  have hH := GeneralPaperBasisStorageRates.determinant_length
  apply GeneralPaperSourceSoftBounds.dominated (g:=fun x => 6+2*binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).H)
  · change Rated (fun x => 6+2*binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).H) 1 0 1
    source_space
  · intro x
    exact GeneralPaperProxyWidths.cap_width x.m x.k

@[fun_prop]
theorem alphabet_length : Rated (fun x => (alphabet x).lambda) 1 0 1 := by
  apply GeneralPaperSourceSoftBounds.dominated (g:=fun x => 24+
    4*((GeneralPaperProxyParameters.prepare x.m x.k).d+2)*binaryWordWidth (x.m+3)+
    2*(x.m*((GeneralPaperComparatorParameters.countRun x.k).power-1)+1)*binaryWordWidth (x.m+2))
  · change Rated (fun x => 24+4*((GeneralPaperProxyParameters.prepare x.m x.k).d+2)*binaryWordWidth (x.m+3)+
      2*(x.m*((GeneralPaperComparatorParameters.countRun x.k).power-1)+1)*binaryWordWidth (x.m+2)) 1 0 1
    source_space
  · intro x
    exact GeneralPaperProxyWidths.lambda_bound x.m x.k

@[fun_prop]
theorem anchor_height : Rated (fun x => GeneralPaperSourceScoreHeights.anchorHeight x.m x.k) 1 0 1 := by
  have hL := alphabet_length
  apply GeneralPaperSourceSoftBounds.dominated (g:=fun x => 2*((alphabet x).lambda+1))
  · change Rated (fun x => 2*((alphabet x).lambda+1)) 1 0 1
    source_space
  · intro x
    exact GeneralPaperSourceAlphabetLower.anchor_height x.m x.k

@[fun_prop]
theorem ray_width : Rated (fun x => GeneralPaperSourceRayStorageWidth.width x.m x.k) 1 0 1 := by
  have hC := cap_word
  have hH := GeneralPaperBasisStorageRates.determinant_length
  change Rated (fun x => 7+6*(78+(3+binaryWordWidth x.m+binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).H+
    2*binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).qbar)+
    14*((GeneralPaperProxyParameters.prepare x.m x.k).d+2)*binaryWordWidth (x.m+3)+
    12*binaryWordWidth ((GeneralPaperProxyParameters.prepare x.m x.k).d+x.m+(GeneralPaperProxyParameters.prepare x.m x.k).K+
      (GeneralPaperProxyParameters.prepare x.m x.k).S+(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows+2))) 1 0 1
  source_space

end Blotto.GeneralPaperSourceSharpOperandRates
