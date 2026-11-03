import Blotto.PlayerSpecificReconstructionFilter

/-! Complete per-leaf executed rational reconstruction: derived cell index,
the actual bit-priced closed CF query, signed decoding and exact acceptance.
The public refinement uses the internally computed original-input cache. -/
namespace Blotto.PlayerSpecificReconstructionLeafExecution
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 1000000

def run (model : RationalCostModel) (p : Data) (cache : PlayerSpecificReconstructionCache.Result) (node : Interval) : Option ℚ×ℕ :=
  let located:=PlayerSpecificReconstructionIndex.run model cache.isolation.magnitude cache.buckets node
  let queried:=GeneralPaperMidpointQueryBits.run model cache.word true cache.denominator cache.buckets located.1 cache.lambda
  let pre:=located.2+queried.2+32*cache.word
  match queried.1.fraction with
  | none => (none,pre+16*cache.word)
  | some f =>
    let decoded:=PlayerSpecificReconstructionDecode.run model cache.isolation.magnitude f
    let accepted:=PlayerSpecificReconstructionFilter.run p node decoded.1
    (accepted.1,pre+decoded.2+price model accepted.2+32*cache.word)

theorem value (model : RationalCostModel) (p : Data) (node : Interval) :
    (run model p (PlayerSpecificReconstructionCache.run model p).1 node).1=PlayerSpecificRationalRoots.reconstruct p node := by
  simp only [run,PlayerSpecificReconstructionIndex.value,GeneralPaperMidpointQueryBits.closed_data,
    PlayerSpecificReconstructionCache.isolation_value,PlayerSpecificIntegerPreparation.magnitude_value,
    PlayerSpecificReconstructionCache.denominator_value,PlayerSpecificReconstructionCache.buckets_value,
    PlayerSpecificReconstructionCache.lambda_value]
  unfold PlayerSpecificRationalRoots.reconstruct PlayerSpecificRationalReconstruction.run
  dsimp only
  cases hfound : (GeneralPaperProxyRootQuery.lookup (PlayerSpecificReconstructionPrecision.denominator p)
    (2^PlayerSpecificReconstructionPrecision.depth p)
    (PlayerSpecificRootCells.index (PlayerSpecificRootMagnitude.rootBound p) (2^PlayerSpecificReconstructionPrecision.depth p) node)
    (PlayerSpecificReconstructionPrecision.depth p+3)).fraction with
  | none => simp only [Option.bind_none]
  | some f =>
    simp only [Option.bind_some,PlayerSpecificReconstructionFilter.value,PlayerSpecificReconstructionDecode.value]

end Blotto.PlayerSpecificReconstructionLeafExecution
