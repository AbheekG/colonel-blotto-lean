import Blotto.GeneralPaperEncodedCatalogueStorage

/-! Native optimizer option caches retain exact tags, mesh and tail ranks.
Ready metadata derives the literal tag words and the constructed mesh word. -/
namespace Blotto.GeneralPaperEncodedOptionCache
open GeneralPaperResponseTag
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def tagBits (W : ℕ) (tag : Tag) : ℕ := rationalWordWidth tag.threshold+1+16*W

def footprint {k K : ℕ} (W : ℕ) (plan : GeneralPaperOrderedNativeOptionProfits.Plan Tag k K) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W (tagBits W) plan.tags+
    GeneralPaperEncodedRankPlans.tailFootprint W plan.tails+(1+binaryWordWidth plan.mesh)+64*W

def profile (W L K k : ℕ) : ℕ :=
  K*(L+17*W+1)+GeneralPaperEncodedRankPlans.tailProfile W K k+(128+8*k)+96*W

theorem mesh_word (k : ℕ) : 1+binaryWordWidth (GeneralPaperSourceParameters.prepare k).meshDenominator≤128+8*k := by
  have h := GeneralPaperNatPowerOperands.power_width 2 (29+k)
  rw [show binaryWordWidth 2=2 by decide] at h
  rw [(GeneralPaperSourceParameters.data k).2.2.2.2.1]
  omega

theorem ready_field {m k : ℕ} (W : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k) (j : Fin m) :
    footprint W (ready.cached.read j)≤profile W (GeneralPaperDecoderControls.operandWidth ready.alphabet.lambda)
      ((GeneralPaperSourceParameters.prepare k).summarySize+2) k := by
  let L := GeneralPaperDecoderControls.operandWidth ready.alphabet.lambda
  let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
  have ht := GeneralPaperEncodedFixedVector.bounded W (L+16*W+1) (tagBits W) (ready.cached.read j).tags (by
    intro i
    have h := rationalWordWidth_of_height (GeneralPaperTagHeight.ready_height ready j i)
    have hWord : rationalWordWidth ((ready.cached.read j).tags.read i).threshold≤L := by
      dsimp only [L,GeneralPaperDecoderControls.operandWidth]
      omega
    unfold tagBits
    omega)
  have hTail : GeneralPaperEncodedRankPlans.tailFootprint W (ready.cached.read j).tails≤GeneralPaperEncodedRankPlans.tailProfile W K k := by
    rw [ready.cached_spec,GeneralPaperOrderedNativeProfitOptimizer.plans,FixedArrayTable.read_ofFn]
    exact GeneralPaperEncodedRankPlans.tail W k (8*ready.alphabet.C) (ready.summaries.read j) (ready.data.codes.read j)
  have hMesh : 1+binaryWordWidth (ready.cached.read j).mesh≤128+8*k := by
    rw [ready.cached_spec,GeneralPaperOrderedNativeProfitOptimizer.plans,FixedArrayTable.read_ofFn]
    exact mesh_word k
  unfold footprint profile
  change _≤K*(L+17*W+1)+GeneralPaperEncodedRankPlans.tailProfile W K k+(128+8*k)+96*W
  dsimp only [K] at hTail ⊢
  nlinarith only [ht,hTail,hMesh]

end Blotto.GeneralPaperEncodedOptionCache
