import Blotto.GeneralPaperEpochCacheCodeWords

/-! The full retained field plan includes its summaries/options, four cell
plans, four occurrence plans and scalar controls. Shared payloads may be
overcounted here; no aliasing or ownership census is executed. -/
namespace Blotto.GeneralPaperEncodedFieldPlanStorage
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def footprint {k : ℕ} (W : ℕ) (plan : GeneralPaperEpochFieldPlan.Plan k) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W plan.pSummary+GeneralPaperEncodedNatArray.footprint W plan.qSummary+
  GeneralPaperEncodedNatArray.footprint W plan.lambdaSummary+GeneralPaperEncodedNatArray.footprint W plan.muSummary+
  GeneralPaperEncodedNatArray.footprint W plan.candidateOptions+GeneralPaperEncodedNatArray.footprint W plan.responseOptions+
  GeneralPaperEncodedCellPlans.unsignedFootprint W plan.pCells+GeneralPaperEncodedCellPlans.unsignedFootprint W plan.qCells+
  GeneralPaperEncodedCellPlans.signedFootprint W plan.lambdaCells+GeneralPaperEncodedCellPlans.signedFootprint W plan.muCells+
  GeneralPaperEncodedRankPlans.lossFootprint W plan.pOccurrences+GeneralPaperEncodedRankPlans.lossFootprint W plan.qOccurrences+
  GeneralPaperEncodedSignedPlans.footprint W plan.lambdaOccurrences+GeneralPaperEncodedSignedPlans.footprint W plan.muOccurrences+
  (1+binaryWordWidth plan.alphabet)+(1+binaryWordWidth plan.candidateCount)+(1+binaryWordWidth plan.responseCount)+256*W

def profile (W lambda k : ℕ) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let K := s+2
  let L := GeneralPaperDecoderControls.operandWidth lambda
  let B := GeneralPaperBatchCounterPrice.limit k
  (4*s+2*K)*(L+W)+2*GeneralPaperEncodedCellPlans.unsignedProfile W L B k+2*GeneralPaperEncodedCellPlans.signedProfile W L B k+
    2*GeneralPaperEncodedRankPlans.lossProfile W s k+2*GeneralPaperEncodedSignedPlans.profile W L s k+L+2*K+4+448*W

theorem prepared {k : ℕ} (W : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) (p q lambda mu : Summary k)
    (candidate response : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ)
    (hp : ∀ i,1+binaryWordWidth (p.read i)≤GeneralPaperDecoderControls.operandWidth a.lambda)
    (hq : ∀ i,1+binaryWordWidth (q.read i)≤GeneralPaperDecoderControls.operandWidth a.lambda)
    (hl : ∀ i,1+binaryWordWidth (lambda.read i)≤GeneralPaperDecoderControls.operandWidth a.lambda)
    (hu : ∀ i,1+binaryWordWidth (mu.read i)≤GeneralPaperDecoderControls.operandWidth a.lambda)
    (hc : ∀ i,1+binaryWordWidth (candidate.read i)≤GeneralPaperDecoderControls.operandWidth a.lambda)
    (hr : ∀ i,1+binaryWordWidth (response.read i)≤GeneralPaperDecoderControls.operandWidth a.lambda) :
    footprint W (GeneralPaperEpochFieldPlan.prepare k (8*a.C) p q lambda mu candidate response)≤profile W a.lambda k := by
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let K := s+2
  let L := GeneralPaperDecoderControls.operandWidth a.lambda
  have bp := GeneralPaperEncodedNatArray.bounded W L p hp
  have bq := GeneralPaperEncodedNatArray.bounded W L q hq
  have bl := GeneralPaperEncodedNatArray.bounded W L lambda hl
  have bu := GeneralPaperEncodedNatArray.bounded W L mu hu
  have bc := GeneralPaperEncodedNatArray.bounded W L candidate hc
  have br := GeneralPaperEncodedNatArray.bounded W L response hr
  have cp := GeneralPaperEncodedCellPlans.source_unsigned W a q lambda candidate
  have cq := GeneralPaperEncodedCellPlans.source_unsigned W a p mu response
  have cl := GeneralPaperEncodedCellPlans.source_signed W a p candidate
  have cu := GeneralPaperEncodedCellPlans.source_signed W a q response
  have op := GeneralPaperEncodedRankPlans.loss W k (8*a.C) q lambda p
  have oq := GeneralPaperEncodedRankPlans.loss W k (8*a.C) p mu q
  have ol := GeneralPaperEncodedSignedPlans.prepared W L k (8*a.C) p lambda hl
  have ou := GeneralPaperEncodedSignedPlans.prepared W L k (8*a.C) q mu hu
  have hU := GeneralPaperEpochCacheCodeWords.unsigned_width a
  have hK := GeneralPaperEncodedFixedVector.annotation K K (Nat.le_refl _)
  change 1+binaryWordWidth (8*a.C)≤L at hU
  dsimp only [footprint,GeneralPaperEpochFieldPlan.prepare]
  change _≤(4*s+2*K)*(L+W)+2*GeneralPaperEncodedCellPlans.unsignedProfile W L (GeneralPaperBatchCounterPrice.limit k) k+
    2*GeneralPaperEncodedCellPlans.signedProfile W L (GeneralPaperBatchCounterPrice.limit k) k+2*GeneralPaperEncodedRankPlans.lossProfile W s k+
    2*GeneralPaperEncodedSignedPlans.profile W L s k+L+2*K+4+448*W
  change GeneralPaperEncodedNatArray.footprint W p≤s*(L+W)+32*W at bp
  change GeneralPaperEncodedNatArray.footprint W q≤s*(L+W)+32*W at bq
  change GeneralPaperEncodedNatArray.footprint W lambda≤s*(L+W)+32*W at bl
  change GeneralPaperEncodedNatArray.footprint W mu≤s*(L+W)+32*W at bu
  change GeneralPaperEncodedNatArray.footprint W candidate≤K*(L+W)+32*W at bc
  change GeneralPaperEncodedNatArray.footprint W response≤K*(L+W)+32*W at br
  nlinarith only [bp,bq,bl,bu,bc,br,cp,cq,cl,cu,op,oq,ol,ou,hU,hK]

theorem actual {m k : ℕ} (W : ℕ) (cache : GeneralPaperCatalogueEpochCache.Cache m k)
    (hc : GeneralPaperCatalogueEpochMetadata.CodesValid cache) (j : Fin m) :
    footprint W (cache.plans.read j)≤profile W cache.alphabet.lambda k := by
  have hca : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  have hra : cache.response.alphabet=cache.alphabet := by rw [cache.response_spec]; rfl
  rw [GeneralPaperCatalogueEpochCache.plan_read]
  apply prepared
  · exact GeneralPaperEpochCacheCodeWords.summary_word cache hc .p j
  · exact GeneralPaperEpochCacheCodeWords.summary_word cache hc .q j
  · exact GeneralPaperEpochCacheCodeWords.summary_word cache hc .lambda j
  · exact GeneralPaperEpochCacheCodeWords.summary_word cache hc .mu j
  · intro i
    have h := GeneralPaperEpochCacheCodeWords.option_word cache.candidate j i
    rw [hca] at h
    exact h
  · intro i
    have h := GeneralPaperEpochCacheCodeWords.option_word cache.response j i
    rw [hra] at h
    exact h

end Blotto.GeneralPaperEncodedFieldPlanStorage
