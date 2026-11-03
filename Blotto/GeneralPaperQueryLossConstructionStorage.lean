import Blotto.GeneralPaperSignedUpdateConstructionStorage

/-! Complete native query-loss construction joins both retained rank
plans, actual partial/final annotation fields and selected child constructors.
Full native records are counted; the operation-price observers stay erased. -/
namespace Blotto.GeneralPaperQueryLossConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def annotationFields {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (cdfSummary tailSummary : Summary k)
    (queries : FixedArrayTable n ℕ) : ℕ :=
  let cdf := (GeneralPaperCDFPairExecution.run true (fun w => w) model.rat W k cdfSummary queries).1.work
  let tails := (GeneralPaperSignedTailExecution.run true (fun w => w) model.rat W k U tailSummary queries).1.work
  fields W [cdf,tails,cdf+tails,cdf+tails+16]

theorem annotation_fields_bound {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (cdfSummary tailSummary : Summary k)
    (queries : FixedArrayTable n ℕ) : annotationFields model W k U cdfSummary tailSummary queries≤
      4*(GeneralPaperSignedTailOperands.width n k U+W)+32*W := by
  have h := GeneralPaperQueryLossPrice.annotation_bound true (fun w => w) model.rat W k U cdfSummary tailSummary queries
  change (GeneralPaperCDFPairExecution.run true (fun w => w) model.rat W k cdfSummary queries).1.work+
    (GeneralPaperSignedTailExecution.run true (fun w => w) model.rat W k U tailSummary queries).1.work+16≤_ at h
  dsimp only [annotationFields]
  apply fields_bound
  intro x hx
  apply (Nat.add_le_add_left (binaryWordWidth_mono (show x≤GeneralPaperSignedTailOperands.magnitude n k from ?_)) 1).trans
    (GeneralPaperSignedTailOperands.word_bound n k U)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with hx|hx|hx|hx
  all_goals (rw [hx]; omega)

def returned {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (cdfSummary tailSummary : Summary k) (queries : FixedArrayTable n ℕ) : ℕ :=
  GeneralPaperEncodedRankPlans.lossFootprint W (GeneralPaperQueryLossExecution.run true (fun w => w) model.rat W k U cdfSummary tailSummary queries).1

def returnedProfile (W n k U : ℕ) : ℕ :=
  GeneralPaperCDFPairConstructionStorage.returnedProfile W n k U+GeneralPaperSignedTailStorage.returnedProfile W n k U+
    GeneralPaperSignedTailOperands.width n k U+64*W

theorem returned_bound {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (cdfSummary tailSummary : Summary k) (queries : FixedArrayTable n ℕ) :
    returned model W k U cdfSummary tailSummary queries≤returnedProfile W n k U := by
  have hc := GeneralPaperCDFPairConstructionStorage.returned_bound model W k U cdfSummary queries
  have ht := GeneralPaperSignedTailStorage.returned_bound model W k U tailSummary queries
  have hw := (Nat.add_le_add_left (binaryWordWidth_mono
    (GeneralPaperQueryLossPrice.annotation_bound true (fun w => w) model.rat W k U cdfSummary tailSummary queries)) 1).trans
      (GeneralPaperSignedTailOperands.word_bound n k U)
  unfold returned returnedProfile GeneralPaperEncodedRankPlans.lossFootprint
  change GeneralPaperCDFPairConstructionStorage.returned model W k cdfSummary queries+
    GeneralPaperSignedTailStorage.returned model W k U tailSummary queries+(1+binaryWordWidth _)+64*W≤_
  omega

def window {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (cdfSummary tailSummary : Summary k) (queries : FixedArrayTable n ℕ)
    (cdfCount tailCount : ℕ) (hc : cdfCount≤n) (ht : tailCount≤n+1) (q : Fin (n+1)) : ℕ :=
  GeneralPaperCDFPairConstructionStorage.window model W k U cdfSummary queries cdfCount hc+
    GeneralPaperSignedTailStorage.window model W k U tailSummary queries tailCount ht q+
    GeneralPaperCDFPairConstructionStorage.returned model W k cdfSummary queries+
    GeneralPaperSignedTailStorage.returned model W k U tailSummary queries+
    annotationFields model W k U cdfSummary tailSummary queries+returned model W k U cdfSummary tailSummary queries+
    fields W [k,U,n]+(GeneralPaperQueryLossExecution.run true (fun w => w) model.rat W k U cdfSummary tailSummary queries).2+256*W

def profile (model : RationalCostModel) (W n k U : ℕ) : ℕ :=
  GeneralPaperCDFPairConstructionStorage.profile model W n k U+GeneralPaperSignedTailStorage.profile model W n k U+
    GeneralPaperCDFPairConstructionStorage.returnedProfile W n k U+GeneralPaperSignedTailStorage.returnedProfile W n k U+
    (4*(GeneralPaperSignedTailOperands.width n k U+W)+32*W)+returnedProfile W n k U+fields W [k,U,n]+
    GeneralPaperQueryLossPrice.profile model.rat W n k U+256*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W k U : ℕ) (cdfSummary tailSummary : Summary k) (queries : FixedArrayTable n ℕ)
    (hCDF : ∀ i,cdfSummary.read i≤U) (hTail : ∀ i,tailSummary.read i≤2*U) (hQueries : ∀ i,queries.read i<U)
    (cdfCount tailCount : ℕ) (hc : cdfCount≤n) (ht : tailCount≤n+1) (q : Fin (n+1)) :
    window model W k U cdfSummary tailSummary queries cdfCount tailCount hc ht q≤profile model W n k U := by
  have hcs := GeneralPaperCDFPairConstructionStorage.bounded model W k U cdfSummary queries hCDF hQueries cdfCount hc
  have hts := GeneralPaperSignedTailStorage.bounded model W k U tailSummary queries hTail (fun i => (hQueries i).le) tailCount ht q
  have hcr := GeneralPaperCDFPairConstructionStorage.returned_bound model W k U cdfSummary queries
  have htr := GeneralPaperSignedTailStorage.returned_bound model W k U tailSummary queries
  have ha := annotation_fields_bound model W k U cdfSummary tailSummary queries
  have hr := returned_bound model W k U cdfSummary tailSummary queries
  have hp := GeneralPaperQueryLossPrice.bit_work model.rat model.monotone W k U cdfSummary tailSummary queries hQueries hCDF hTail
  unfold window profile
  omega

end Blotto.GeneralPaperQueryLossConstructionStorage
