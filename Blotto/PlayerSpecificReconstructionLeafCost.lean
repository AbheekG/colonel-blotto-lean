import Blotto.PlayerSpecificReconstructionLeafBounds

/-! Complete cost of each actual reconstruction leaf, deriving CF input
sizes, returned fraction bounds and decoded/filter heights from original
input and the computed cache. No per-leaf aggregate oracle is supplied. -/
namespace Blotto.PlayerSpecificReconstructionLeafCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificIsolationState PlayerSpecificRationalMagnitude
open PlayerSpecificReconstructionLeafBounds PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem run_cost (model : RationalCostModel) (p : Data) (hlen : p.length≤4) (node : Interval)
    (hnode : node∈PlayerSpecificRationalRoots.intervals p) :
    (PlayerSpecificReconstructionLeafExecution.run model p (PlayerSpecificReconstructionCache.run model p).1 node).2≤
      20000000*(PlayerSpecificIntegerBudget.height (inputHeight p)+1)*model.rat (PlayerSpecificIntegerBudget.width (inputHeight p)) := by
  let H:=inputHeight p
  let J:=PlayerSpecificIntegerBudget.height H
  let W:=PlayerSpecificIntegerBudget.width H
  let cache:=(PlayerSpecificReconstructionCache.run model p).1
  let located:=PlayerSpecificReconstructionIndex.run model cache.isolation.magnitude cache.buckets node
  let queried:=GeneralPaperMidpointQueryBits.run model cache.word true cache.denominator cache.buckets located.1 cache.lambda
  have hM : binaryWordWidth cache.isolation.magnitude=2*H+3 := by
    rw [magnitude_value,PlayerSpecificIsolationDepthHeight.root_width]
  have hC : binaryWordWidth cache.buckets=PlayerSpecificReconstructionPrecision.depth p+1 := by
    rw [PlayerSpecificReconstructionCache.buckets_value,PlayerSpecificIsolationDepthHeight.two_power_width]
  have hD : binaryWordWidth cache.denominator=7*H+4 := by
    rw [PlayerSpecificReconstructionCache.denominator_value,PlayerSpecificReconstructionPrecision.denominator_width]
  have hidxM : binaryWordWidth cache.isolation.magnitude≤ indexHeight p := by rw [hM]; unfold indexHeight; omega
  have hidxC : binaryWordWidth cache.buckets≤ indexHeight p := by rw [hC]; unfold indexHeight; omega
  have hidxT : 2≤ indexHeight p := by unfold indexHeight; omega
  have he:=endpoint_heights p node hnode
  have hi:=PlayerSpecificReconstructionIndex.run_cost model cache.isolation.magnitude cache.buckets node (indexHeight p) hidxT he.1 hidxM hidxC
  have hiW : 32*(indexHeight p+1)≤W := by
    have h : indexHeight p≤J := (index_height p).trans (height_bound p hlen)
    unfold W PlayerSpecificIntegerBudget.width
    omega
  have hip:=hi.trans (Nat.mul_le_mul_left 5000 (model.monotone hiW))
  have hqdata:=query_data model p node hnode
  have hquery:=GeneralPaperMidpointQueryBits.work model cache.word cache.denominator cache.buckets located.1 cache.lambda true
    hqdata.1 hqdata.2.1 hqdata.2.2.1 hqdata.2.2.2
  have hword : cache.word≤W := PlayerSpecificReconstructionCacheBudget.source_word model p hlen
  have hwordP:=hword.trans (model.word_le W)
  have hqueryWidth : model.rat (GeneralPaperCFOperandPrice.width cache.lambda cache.denominator)≤model.rat W :=
    model.monotone ((PlayerSpecificReconstructionCacheBudget.query_width model p).trans hword)
  have hsum : cache.word+model.rat (GeneralPaperCFOperandPrice.width cache.lambda cache.denominator)≤2*model.rat W := by omega
  have hLambda : cache.lambda+3≤3*(J+1) := by
    have hcap : PlayerSpecificReconstructionPrecision.depth p+3≤J := (PlayerSpecificReconstructionCacheBudget.controls p hlen).2.2.2.2
    rw [PlayerSpecificReconstructionCache.lambda_value]
    omega
  have hfactor:=Nat.mul_le_mul (Nat.mul_le_mul_left 2097152 hLambda) hsum
  have hqp : queried.2≤12582912*(J+1)*model.rat W := by
    exact hquery.trans (hfactor.trans_eq (by ring))
  have hcf:=GeneralPaperMidpointQueryBits.closed_data model cache.word cache.denominator cache.buckets located.1 cache.lambda
  rw [PlayerSpecificReconstructionLeafExecution.run]
  dsimp only
  cases hs : queried.1.fraction with
  | none =>
    have hword16:=Nat.mul_le_mul_left 16 hwordP
    have hword32:=Nat.mul_le_mul_left 32 hwordP
    nlinarith only [hip,hqp,hword16,hword32]
  | some f =>
    have hsome : (GeneralPaperProxyRootQuery.lookup cache.denominator cache.buckets located.1 cache.lambda).fraction=some f := by
      rw [←hcf]
      exact hs
    have hsound:=GeneralPaperProxyRootQuery.sound cache.denominator cache.buckets located.1 cache.lambda f hsome
    have hindex : located.1<cache.buckets := hqdata.2.2.1
    have hupper : GeneralPaperBucketGeometry.upper cache.buckets located.1≤1 := by
      unfold GeneralPaperBucketGeometry.upper
      apply (div_le_one (by exact_mod_cast hqdata.2.1 : (0:ℚ)<cache.buckets)).mpr
      exact_mod_cast (show located.1+1≤cache.buckets by omega)
    have hnum : f.num≤f.den := Farey.num_le_den f (hsound.2.2.trans hupper)
    have hfDen : binaryWordWidth f.den≤decodeHeight p := by
      have h:=binaryWordWidth_mono hsound.1
      rw [hD] at h
      unfold decodeHeight
      omega
    have hfNum : binaryWordWidth f.num≤decodeHeight p := (binaryWordWidth_mono hnum).trans hfDen
    have hfM : binaryWordWidth cache.isolation.magnitude≤decodeHeight p := by rw [hM]; unfold decodeHeight; omega
    have hdecT : 2≤decodeHeight p := by unfold decodeHeight; omega
    let decoded:=PlayerSpecificReconstructionDecode.run model cache.isolation.magnitude f
    let accepted:=PlayerSpecificReconstructionFilter.run p node decoded.1
    have hd:=PlayerSpecificReconstructionDecode.run_cost model cache.isolation.magnitude f (decodeHeight p) hdecT hfM hfNum hfDen
    have hdW : 32*(decodeHeight p+1)≤W := by
      have h : decodeHeight p≤J := (decode_height p).trans (height_bound p hlen)
      unfold W PlayerSpecificIntegerBudget.width
      omega
    have hdp:=hd.trans (Nat.mul_le_mul_left 5000 (model.monotone hdW))
    have hdH : RationalHeight decoded.1 (height p) :=
      (PlayerSpecificReconstructionDecode.height model cache.isolation.magnitude f (decodeHeight p) hdecT hfM hfNum hfDen).mono (decoded_height p)
    have hfilter:=PlayerSpecificReconstructionFilter.run_cost model p node decoded.1 (height p)
      (mono (PlayerSpecificPolynomialHeights.input_height p) (input_height p)) hlen
      (he.1.mono (index_height p)) (he.2.mono (index_height p)) hdH
    have hfp:=hfilter.trans (Nat.mul_le_mul_left 1000 (model.monotone (source_width p hlen)))
    have hword32:=Nat.mul_le_mul_left 32 hwordP
    nlinarith only [hip,hqp,hdp,hfp,hword32]

end Blotto.PlayerSpecificReconstructionLeafCost
