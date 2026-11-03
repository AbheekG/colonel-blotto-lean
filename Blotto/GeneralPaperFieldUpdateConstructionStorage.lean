import Blotto.GeneralPaperLevelArrayStorage

/-! Complete eight-array delta and level-advance construction. Full native
returns, borrowed choice reads, outer controls and every active child are
joined. Native cell counts derive source capacities; intermediate updated
levels use the proved sum bound rather than assuming a reached next state. -/
namespace Blotto.GeneralPaperFieldUpdateConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
open GeneralPaperCatalogueOccurrenceHistory (Learner block)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem field_word {k : ℕ} (W m lambda Qv V : ℕ) (state : State k)
    (hc : GeneralPaperEncodedEpochLevels.Counts state) (hv : Bounded state V)
    (hw : natBits V≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) :
    GeneralPaperEncodedEpochLevels.fieldFootprint W state≤GeneralPaperEncodedEpochLevels.fieldProfile W m lambda k Qv := by
  have hbound : ∀ {n : ℕ} (a : FixedArrayTable n ℕ), (∀ i,a.read i≤V) →
      GeneralPaperEncodedNatArray.footprint W a≤n*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+32*W := by
    intro n a ha
    exact GeneralPaperEncodedNatArray.bounded W _ a (fun i => (Nat.add_le_add_left (binaryWordWidth_mono (ha i)) 1).trans hw)
  have hp := hbound state.pOccurrences hv.1
  have hq := hbound state.qOccurrences hv.2.1
  have hl := hbound state.lambdaOccurrences hv.2.2.1
  have hm := hbound state.muOccurrences hv.2.2.2.1
  have pc := (hbound state.pCells hv.2.2.2.2.1).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc.1) _)
  have qc := (hbound state.qCells hv.2.2.2.2.2.1).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc.2.1) _)
  have lc := (hbound state.lambdaCells hv.2.2.2.2.2.2.1).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc.2.2.1) _)
  have mc := (hbound state.muCells hv.2.2.2.2.2.2.2).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc.2.2.2) _)
  unfold GeneralPaperEncodedEpochLevels.fieldFootprint GeneralPaperEncodedEpochLevels.fieldProfile
  nlinarith only [hp,hq,hl,hm,pc,qc,lc,mc]

def deltaWindow {k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (state : State k) (snapshot : Snapshot k)
    (choice : Choice state.plan) (count : ℕ) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let p := state.plan
  GeneralPaperDeltaArrayStorage.unsignedWindow model W mesh false snapshot.q.cdf snapshot.lambda.cdf p.pOccurrences (min count s) (Nat.min_le_right ..)+
    GeneralPaperDeltaArrayStorage.unsignedWindow model W mesh true snapshot.p.cdf snapshot.mu.cdf p.qOccurrences (min count s) (Nat.min_le_right ..)+
    GeneralPaperDeltaArrayStorage.signedWindow model W mesh p.alphabet choice.candidateBid snapshot.p.cdf p.lambdaOccurrences (min count s) (Nat.min_le_right ..)+
    GeneralPaperDeltaArrayStorage.signedWindow model W mesh p.alphabet choice.responseBid snapshot.q.cdf p.muOccurrences (min count s) (Nat.min_le_right ..)+
    GeneralPaperDeltaArrayStorage.unsignedWindow model W mesh false snapshot.q.cdf snapshot.lambda.cdf p.pCells.ranks (min count p.pCells.partition.count) (Nat.min_le_right ..)+
    GeneralPaperDeltaArrayStorage.unsignedWindow model W mesh true snapshot.p.cdf snapshot.mu.cdf p.qCells.ranks (min count p.qCells.partition.count) (Nat.min_le_right ..)+
    GeneralPaperDeltaArrayStorage.signedWindow model W mesh p.alphabet choice.candidateBid snapshot.p.cdf p.lambdaCells.ranks (min count p.lambdaCells.partition.count) (Nat.min_le_right ..)+
    GeneralPaperDeltaArrayStorage.signedWindow model W mesh p.alphabet choice.responseBid snapshot.q.cdf p.muCells.ranks (min count p.muCells.partition.count) (Nat.min_le_right ..)+
    GeneralPaperEncodedEpochLevels.fieldFootprint W (GeneralPaperEncodedEpochLevels.deltaView
      (GeneralPaperFieldDeltaExecution.run true (fun w => w) model.rat W mesh state snapshot choice).1)+
    fields W [p.alphabet,choice.candidateBid,choice.responseBid]+
    fields W [p.candidateCount,p.responseCount,choice.candidate.val,choice.response.val]+
    fields W [8,s,p.pCells.partition.count,p.qCells.partition.count,p.lambdaCells.partition.count,p.muCells.partition.count]+256*W

def deltaProfile (model : RationalCostModel) (W m lambda k Qv candidateCount responseCount : ℕ) : ℕ :=
  let B := GeneralPaperBatchCounterPrice.limit k
  let L := GeneralPaperDecoderControls.operandWidth lambda
  4*GeneralPaperDeltaArrayStorage.unsignedProfile model W m lambda k Qv B+
    4*GeneralPaperDeltaArrayStorage.signedProfile model W m lambda k Qv B+
    GeneralPaperEncodedEpochLevels.fieldProfile W m lambda k Qv+
    (3*(L+W)+32*W)+(4*(natBits (candidateCount+1)+natBits (responseCount+1)+W)+32*W)+
    (6*(natBits (B+8)+W)+32*W)+256*W

theorem delta_bounded {k : ℕ} (model : RationalCostModel) (W m lambda Qv mesh : ℕ) (state : State k) (snapshot : Snapshot k)
    (choice : Choice state.plan) (count : ℕ)
    (hmesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hg : ∀ learner,GeneralPaperMeshPrefixInvariant.Good m lambda k Qv (block learner snapshot).cdf)
    (hsafe : GeneralPaperDeltaPlanBounds.PlanSafe lambda state.plan)
    (hc : GeneralPaperEncodedEpochLevels.Counts state) (hpositive : Positive snapshot) (hcoherent : Coherent snapshot) :
    deltaWindow model W mesh state snapshot choice count≤deltaProfile model W m lambda k Qv state.plan.candidateCount state.plan.responseCount := by
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let B := GeneralPaperBatchCounterPrice.limit k
  have hs : s≤B := by unfold s B GeneralPaperBatchCounterPrice.limit; omega
  have hu : ∀ {n : ℕ} (response : Bool) (cp tp : GeneralPaperUnsignedCellConstancy.Prefix k)
      (p : GeneralPaperQueryLossCounts.Plan k n), n≤B →
      GeneralPaperMeshPrefixInvariant.Good m lambda k Qv cp → GeneralPaperMeshPrefixInvariant.Good m lambda k Qv tp →
      GeneralPaperDeltaArrayStorage.unsignedWindow model W mesh response cp tp p (min count n) (Nat.min_le_right ..)≤
        GeneralPaperDeltaArrayStorage.unsignedProfile model W m lambda k Qv B := by
    intro n response cp tp p hn hcp htp
    exact (GeneralPaperDeltaArrayStorage.unsigned_bounded model W m lambda Qv mesh response cp tp p _ _ hmesh hcp htp).trans
      (GeneralPaperDeltaArrayStorage.unsigned_mono model W m lambda k Qv n B hn)
  have hz : ∀ {n : ℕ} (bid : ℕ) (cp : GeneralPaperUnsignedCellConstancy.Prefix k)
      (p : GeneralPaperSignedUpdatePlan.Plan k n), n≤B →
      GeneralPaperMeshPrefixInvariant.Good m lambda k Qv cp → bid≤2^(lambda+1) → GeneralPaperDeltaPlanBounds.SignedSafe lambda p →
      GeneralPaperDeltaArrayStorage.signedWindow model W mesh state.plan.alphabet bid cp p (min count n) (Nat.min_le_right ..)≤
        GeneralPaperDeltaArrayStorage.signedProfile model W m lambda k Qv B := by
    intro n bid cp p hn hcp hbid hp
    exact (GeneralPaperDeltaArrayStorage.signed_bounded model W m lambda Qv mesh _ bid cp p _ _ hmesh hcp hsafe.alphabet hbid hp).trans
      (GeneralPaperDeltaArrayStorage.signed_mono model W m lambda k Qv n B hn)
  have po := hu false snapshot.q.cdf snapshot.lambda.cdf state.plan.pOccurrences hs (hg .q) (hg .lambda)
  have qo := hu true snapshot.p.cdf snapshot.mu.cdf state.plan.qOccurrences hs (hg .p) (hg .mu)
  have lo := hz choice.candidateBid snapshot.p.cdf state.plan.lambdaOccurrences hs (hg .p) (hsafe.candidate choice.candidate) hsafe.lambdaOccurrences
  have mo := hz choice.responseBid snapshot.q.cdf state.plan.muOccurrences hs (hg .q) (hsafe.response choice.response) hsafe.muOccurrences
  have pc := hu false snapshot.q.cdf snapshot.lambda.cdf state.plan.pCells.ranks hc.1 (hg .q) (hg .lambda)
  have qc := hu true snapshot.p.cdf snapshot.mu.cdf state.plan.qCells.ranks hc.2.1 (hg .p) (hg .mu)
  have lc := hz choice.candidateBid snapshot.p.cdf state.plan.lambdaCells.ranks hc.2.2.1 (hg .p) (hsafe.candidate choice.candidate) hsafe.lambdaCells
  have mc := hz choice.responseBid snapshot.q.cdf state.plan.muCells.ranks hc.2.2.2 (hg .q) (hsafe.response choice.response) hsafe.muCells
  have hd := GeneralPaperFieldDeltaExecution.returned_bound true (fun w => w) model.rat W mesh state snapshot choice hmesh hpositive hcoherent
  have hw : natBits (8*(GeneralPaperSourceParameters.prepare k).meshDenominator)≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv :=
    (Nat.add_le_add_left (binaryWordWidth_mono (show 8*(GeneralPaperSourceParameters.prepare k).meshDenominator≤
      GeneralPaperIncrementPrice.cap (GeneralPaperSourceParameters.prepare k).meshDenominator by unfold GeneralPaperIncrementPrice.cap; omega)) 1).trans
        (GeneralPaperIncrementPrice.operand_word m lambda k Qv)
  have hr := field_word W m lambda Qv _ (GeneralPaperEncodedEpochLevels.deltaView
    (GeneralPaperFieldDeltaExecution.run true (fun w => w) model.rat W mesh state snapshot choice).1) hc hd hw
  have hcodes := fields_bound W (GeneralPaperDecoderControls.operandWidth lambda) [state.plan.alphabet,choice.candidateBid,choice.responseBid] (by
    intro x hx; apply GeneralPaperSignedDeltaStepPrice.code_word lambda
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact hsafe.alphabet
    · exact hsafe.candidate choice.candidate
    · exact hsafe.response choice.response)
  have hchoices := fields_bound W (natBits (state.plan.candidateCount+1)+natBits (state.plan.responseCount+1))
    [state.plan.candidateCount,state.plan.responseCount,choice.candidate.val,choice.response.val] (by
      intro x hx
      have hcw := GeneralPaperRankStorageMonotonicity.nat_word state.plan.candidateCount (state.plan.candidateCount+1) (by omega)
      have hrw := GeneralPaperRankStorageMonotonicity.nat_word state.plan.responseCount (state.plan.responseCount+1) (by omega)
      have hcq := GeneralPaperRankStorageMonotonicity.nat_word choice.candidate.val (state.plan.candidateCount+1) (by have := choice.candidate.isLt; omega)
      have hrq := GeneralPaperRankStorageMonotonicity.nat_word choice.response.val (state.plan.responseCount+1) (by have := choice.response.isLt; omega)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl
      all_goals omega)
  have hcontrols := fields_bound W (natBits (B+8)) [8,s,state.plan.pCells.partition.count,state.plan.qCells.partition.count,
    state.plan.lambdaCells.partition.count,state.plan.muCells.partition.count] (by
      have hpc := hc.1
      have hqc := hc.2.1
      have hlc := hc.2.2.1
      have hmc := hc.2.2.2
      intro x hx; apply GeneralPaperRankStorageMonotonicity.nat_word
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals omega)
  simp only [List.length_cons,List.length_nil] at hcodes hchoices hcontrols
  dsimp only [deltaWindow,deltaProfile]
  dsimp only [s,B] at po qo lo mo pc qc lc mc hcontrols
  omega

def advanceWindow {k : ℕ} (model : RationalCostModel) (W : ℕ) (state : State k) (delta : Deltas state) (count : ℕ) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  GeneralPaperLevelArrayStorage.window model W state.pOccurrences delta.pOccurrences (min count s) (Nat.min_le_right ..)+
    GeneralPaperLevelArrayStorage.window model W state.qOccurrences delta.qOccurrences (min count s) (Nat.min_le_right ..)+
    GeneralPaperLevelArrayStorage.window model W state.lambdaOccurrences delta.lambdaOccurrences (min count s) (Nat.min_le_right ..)+
    GeneralPaperLevelArrayStorage.window model W state.muOccurrences delta.muOccurrences (min count s) (Nat.min_le_right ..)+
    GeneralPaperLevelArrayStorage.window model W state.pCells delta.pCells (min count state.plan.pCells.partition.count) (Nat.min_le_right ..)+
    GeneralPaperLevelArrayStorage.window model W state.qCells delta.qCells (min count state.plan.qCells.partition.count) (Nat.min_le_right ..)+
    GeneralPaperLevelArrayStorage.window model W state.lambdaCells delta.lambdaCells (min count state.plan.lambdaCells.partition.count) (Nat.min_le_right ..)+
    GeneralPaperLevelArrayStorage.window model W state.muCells delta.muCells (min count state.plan.muCells.partition.count) (Nat.min_le_right ..)+
    GeneralPaperEncodedEpochLevels.fieldFootprint W (GeneralPaperEpochFieldAdvancePrice.run true (fun w => w) model.rat W state delta).1+256*W

def advanceProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  8*GeneralPaperLevelArrayStorage.profile model W m lambda k Qv (GeneralPaperBatchCounterPrice.limit k)+
    GeneralPaperEncodedEpochLevels.fieldProfile W m lambda k Qv+256*W

theorem advance_bounded {k : ℕ} (model : RationalCostModel) (W m lambda Qv : ℕ) (state : State k) (delta : Deltas state) (count : ℕ)
    (hc : GeneralPaperEncodedEpochLevels.Counts state) (hs : Bounded state (GeneralPaperPowerPrecision.levelBound lambda k))
    (hd : delta.Bounded (8*(GeneralPaperSourceParameters.prepare k).meshDenominator)) :
    advanceWindow model W state delta count≤advanceProfile model W m lambda k Qv := by
  let B := GeneralPaperBatchCounterPrice.limit k
  have hS : (GeneralPaperSourceParameters.prepare k).summarySize≤B := by unfold B GeneralPaperBatchCounterPrice.limit; omega
  have harray : ∀ {n : ℕ} (a b : FixedArrayTable n ℕ), n≤B →
      (∀ r,a.read r≤GeneralPaperPowerPrecision.levelBound lambda k) →
      (∀ r,b.read r≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator) →
      GeneralPaperLevelArrayStorage.window model W a b (min count n) (Nat.min_le_right ..)≤GeneralPaperLevelArrayStorage.profile model W m lambda k Qv B := by
    intro n a b hn ha hb
    exact (GeneralPaperLevelArrayStorage.bounded model W m lambda k Qv a b _ _ ha hb).trans
      (GeneralPaperLevelArrayStorage.profile_mono model W m lambda k Qv n B hn)
  have po := harray state.pOccurrences delta.pOccurrences hS hs.1 hd.1
  have qo := harray state.qOccurrences delta.qOccurrences hS hs.2.1 hd.2.1
  have lo := harray state.lambdaOccurrences delta.lambdaOccurrences hS hs.2.2.1 hd.2.2.1
  have mo := harray state.muOccurrences delta.muOccurrences hS hs.2.2.2.1 hd.2.2.2.1
  have pc := harray state.pCells delta.pCells hc.1 hs.2.2.2.2.1 hd.2.2.2.2.1
  have qc := harray state.qCells delta.qCells hc.2.1 hs.2.2.2.2.2.1 hd.2.2.2.2.2.1
  have lc := harray state.lambdaCells delta.lambdaCells hc.2.2.1 hs.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.1
  have mc := harray state.muCells delta.muCells hc.2.2.2 hs.2.2.2.2.2.2.2 hd.2.2.2.2.2.2.2
  have hreturn := GeneralPaperEpochFieldAdvancePrice.returned_bounded true (fun w => w) model.rat W _ _ state delta hs hd
  have hr := field_word W m lambda Qv _ (GeneralPaperEpochFieldAdvancePrice.run true (fun w => w) model.rat W state delta).1 hc hreturn
    (GeneralPaperEpochLevelPrice.operand_word m lambda k Qv)
  dsimp only [advanceWindow,advanceProfile]
  dsimp only [B] at po qo lo mo pc qc lc mc
  omega

end Blotto.GeneralPaperFieldUpdateConstructionStorage
