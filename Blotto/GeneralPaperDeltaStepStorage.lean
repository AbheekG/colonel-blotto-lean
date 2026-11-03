import Blotto.GeneralPaperIncrementStorage

/-! Complete unsigned/signed update callback windows retain their query
children, integer increments, native results, partial/final annotations,
index controls and primitive scratch. Signed code/bid words stay separate
from short mesh counters. Arrays and prepared plans are borrowed. -/
namespace Blotto.GeneralPaperDeltaStepStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshPrefixInvariant (Good)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem unsigned_value {n k : ℕ} (model : RationalCostModel) (W m lambda Qv mesh : ℕ) (response : Bool)
    (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hc : Good m lambda k Qv cdfPrefix) (ht : Good m lambda k Qv tailPrefix) :
    (GeneralPaperUnsignedDeltaStepPrice.run true model.rat W mesh response cdfPrefix tailPrefix plan q).1≤8*mesh := by
  let counts := (GeneralPaperMeshPairExecution.counts true model.rat W mesh cdfPrefix tailPrefix plan q).1
  have hb := GeneralPaperMeshCountBounds.counts_bound true model.rat W m lambda Qv mesh cdfPrefix tailPrefix plan q hm hc ht
  change GeneralPaperQueryLossCounts.Bounds k counts at hb
  unfold GeneralPaperQueryLossCounts.Bounds at hb
  rw [←hm] at hb
  cases response
  all_goals
    change _*mesh+2*counts.positive-(counts.lower+counts.upper+2*counts.negative)≤8*mesh
    simp only [Bool.false_eq_true,ite_false,ite_true]
    omega

theorem signed_value {n k : ℕ} (model : RationalCostModel) (W m lambda Qv mesh U bid : ℕ)
    (prefixes : Prefix k) (plan : GeneralPaperSignedUpdatePlan.Plan k n) (q : Fin n)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hg : Good m lambda k Qv prefixes) :
    (GeneralPaperSignedDeltaStepPrice.run true model.rat W mesh U bid prefixes plan q).1.increment≤8*mesh := by
  let count := (GeneralPaperCachedMeshPrefixQuery.cached true model.rat W mesh prefixes plan.ranks q).1.quotient
  have hc : count≤mesh := GeneralPaperMeshCountBounds.cached_prefix_bound true model.rat W m lambda Qv mesh prefixes plan.ranks q hm hg
  change 4*mesh+(if decide (plan.codes.read q<U) then 2*(if decide (bid≤plan.positions.read q) then mesh else 0) else 2*count)-
    (if decide (plan.codes.read q<U) then 2*count else 2*(if decide (bid≤plan.positions.read q) then mesh else 0))≤8*mesh
  split_ifs <;> omega

def unsignedWindow {n k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (response : Bool)
    (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n) : ℕ :=
  let counts := GeneralPaperMeshPairExecution.counts true model.rat W mesh cdfPrefix tailPrefix plan q
  let found := GeneralPaperUnsignedDeltaStepPrice.run true model.rat W mesh response cdfPrefix tailPrefix plan q
  GeneralPaperMeshPairStorage.countsWindow model W mesh cdfPrefix tailPrefix plan q+
    GeneralPaperIncrementStorage.unsignedWindow model W response mesh counts.1.lower counts.1.upper counts.1.positive counts.1.negative+
    natBits found.1+fields W [counts.1.work,24,counts.1.work+24]+fields W [n,q.val]+found.2+256*W

def unsignedProfile (model : RationalCostModel) (W m lambda k Qv n : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  GeneralPaperMeshPairStorage.countsProfile model W m lambda k Qv n+
    GeneralPaperIncrementStorage.unsignedProfile model W m lambda k Qv+
    H+(3*(H+W)+32*W)+(2*(natBits (n+1)+W)+32*W)+
    GeneralPaperUnsignedDeltaStepPrice.profile model.rat W m lambda k Qv+256*W

theorem unsigned_bounded {n k : ℕ} (model : RationalCostModel) (W m lambda Qv mesh : ℕ) (response : Bool)
    (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hc : Good m lambda k Qv cdfPrefix) (ht : Good m lambda k Qv tailPrefix) :
    unsignedWindow model W mesh response cdfPrefix tailPrefix plan q≤unsignedProfile model W m lambda k Qv n := by
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let counts := GeneralPaperMeshPairExecution.counts true model.rat W mesh cdfPrefix tailPrefix plan q
  let found := GeneralPaperUnsignedDeltaStepPrice.run true model.rat W mesh response cdfPrefix tailPrefix plan q
  have hq := GeneralPaperMeshPairStorage.counts_bounded model W m lambda Qv mesh cdfPrefix tailPrefix plan q hm hc ht
  have hb := GeneralPaperMeshCountBounds.counts_bound true model.rat W m lambda Qv mesh cdfPrefix tailPrefix plan q hm hc ht
  change GeneralPaperQueryLossCounts.Bounds k counts.1 at hb
  unfold GeneralPaperQueryLossCounts.Bounds at hb
  rw [←hm] at hb
  have hi := GeneralPaperIncrementStorage.unsigned_bounded model W m lambda k Qv mesh counts.1.lower counts.1.upper counts.1.positive counts.1.negative response hm hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
  have hv := unsigned_value model W m lambda Qv mesh response cdfPrefix tailPrefix plan q hm hc ht
  have hret : natBits found.1≤H := (Nat.add_le_add_left (binaryWordWidth_mono
    (show found.1≤GeneralPaperIncrementPrice.cap mesh by unfold GeneralPaperIncrementPrice.cap; exact hv.trans (by omega))) 1).trans (by rw [hm]; exact GeneralPaperIncrementPrice.operand_word m lambda k Qv)
  have hwork : counts.1.work=48*(30+k)+232 := by
    rw [GeneralPaperMeshPairExecution.counts_data true model.rat W mesh cdfPrefix tailPrefix plan q hm,GeneralPaperQueryLossCounts.evaluate_work]
  have hf := GeneralPaperMeshPairStorage.metadata_fields W m lambda k Qv [counts.1.work,24,counts.1.work+24] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    all_goals (unfold GeneralPaperMeshQueryMetadata.cap; omega))
  have hind := GeneralPaperMeshPairStorage.index_fields W n [n,q.val] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · omega
    · exact q.isLt.le.trans (by omega))
  have hprice := GeneralPaperUnsignedDeltaStepPrice.bit_work model.rat model.monotone W m lambda Qv mesh response cdfPrefix tailPrefix plan q hm hc ht
  dsimp only [unsignedWindow,unsignedProfile]
  dsimp only [counts,found] at hi hf hret
  simp only [List.length_cons,List.length_nil] at hf hind
  omega

def signedRecord (W : ℕ) (r : GeneralPaperSignedUpdatePlan.Result) : ℕ := fields W [r.increment,r.count,r.work]+4+64*W

def signedWindow {n k : ℕ} (model : RationalCostModel) (W mesh U bid : ℕ)
    (prefixes : Prefix k) (plan : GeneralPaperSignedUpdatePlan.Plan k n) (q : Fin n) : ℕ :=
  let queried := GeneralPaperCachedMeshPrefixQuery.cached true model.rat W mesh prefixes plan.ranks q
  let positive := decide (plan.codes.read q<U)
  let hit := decide (bid≤plan.positions.read q)
  let found := GeneralPaperSignedDeltaStepPrice.run true model.rat W mesh U bid prefixes plan q
  GeneralPaperCachedMeshQueryStorage.prefixWindow model W mesh prefixes plan.ranks q+
    GeneralPaperIncrementStorage.signedWindow model W mesh queried.1.quotient positive hit+
    signedRecord W found.1+fields W [U,bid,plan.codes.read q,plan.positions.read q]+
    fields W [queried.1.work,24,queried.1.work+24]+fields W [n,q.val]+found.2+256*W

def signedProfile (model : RationalCostModel) (W m lambda k Qv n : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let L := GeneralPaperDecoderControls.operandWidth lambda
  GeneralPaperCachedMeshQueryStorage.prefixProfile model W m lambda k Qv n+
    GeneralPaperIncrementStorage.signedProfile model W m lambda k Qv+
    (3*(H+W)+32*W+4+64*W)+(4*(L+W)+32*W)+
    (3*(H+W)+32*W)+(2*(natBits (n+1)+W)+32*W)+
    GeneralPaperSignedDeltaStepPrice.profile model.rat W m lambda k Qv+256*W

theorem signed_bounded {n k : ℕ} (model : RationalCostModel) (W m lambda Qv mesh U bid : ℕ)
    (prefixes : Prefix k) (plan : GeneralPaperSignedUpdatePlan.Plan k n) (q : Fin n)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hg : Good m lambda k Qv prefixes)
    (hU : U≤2^(lambda+1)) (hbid : bid≤2^(lambda+1))
    (hcode : plan.codes.read q≤2^(lambda+1)) (hpos : plan.positions.read q≤2^(lambda+1)) :
    signedWindow model W mesh U bid prefixes plan q≤signedProfile model W m lambda k Qv n := by
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let L := GeneralPaperDecoderControls.operandWidth lambda
  let queried := GeneralPaperCachedMeshPrefixQuery.cached true model.rat W mesh prefixes plan.ranks q
  let found := GeneralPaperSignedDeltaStepPrice.run true model.rat W mesh U bid prefixes plan q
  have hq := GeneralPaperCachedMeshQueryStorage.prefix_bounded model W m lambda Qv mesh prefixes plan.ranks q hm hg
  have hcount := GeneralPaperMeshCountBounds.cached_prefix_bound true model.rat W m lambda Qv mesh prefixes plan.ranks q hm hg
  have hi := GeneralPaperIncrementStorage.signed_bounded model W m lambda k Qv mesh queried.1.quotient
    (decide (plan.codes.read q<U)) (decide (bid≤plan.positions.read q)) hm hcount
  have hv := signed_value model W m lambda Qv mesh U bid prefixes plan q hm hg
  have hret : natBits found.1.increment≤H := (Nat.add_le_add_left (binaryWordWidth_mono
    (show found.1.increment≤GeneralPaperIncrementPrice.cap mesh by unfold GeneralPaperIncrementPrice.cap; exact hv.trans (by omega))) 1).trans (by rw [hm]; exact GeneralPaperIncrementPrice.operand_word m lambda k Qv)
  have hcw : natBits found.1.count≤H := GeneralPaperMeshPairStorage.count_word m lambda k Qv mesh _ hm hcount
  have hwork : queried.1.work=12*(30+k)+42 := by
    rw [GeneralPaperCachedMeshPrefixQuery.cached_data true model.rat W mesh prefixes plan.ranks q hm,GeneralPaperRankedCDFQuery.cached_work]
  have hww : natBits found.1.work≤H := (Nat.add_le_add_left (binaryWordWidth_mono
    (show found.1.work≤GeneralPaperMeshQueryMetadata.cap k by
      change queried.1.work+24≤_; unfold GeneralPaperMeshQueryMetadata.cap; omega)) 1).trans
        (GeneralPaperMeshQueryMetadata.operand_word m lambda k Qv)
  have hr := fields_bound W H [found.1.increment,found.1.count,found.1.work] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact hret
    · exact hcw
    · exact hww)
  have hcodes := fields_bound W L [U,bid,plan.codes.read q,plan.positions.read q] (by
    intro x hx
    apply GeneralPaperSignedDeltaStepPrice.code_word lambda
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    all_goals assumption)
  have hf := GeneralPaperMeshPairStorage.metadata_fields W m lambda k Qv [queried.1.work,24,queried.1.work+24] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    all_goals (unfold GeneralPaperMeshQueryMetadata.cap; omega))
  have hind := GeneralPaperMeshPairStorage.index_fields W n [n,q.val] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · omega
    · exact q.isLt.le.trans (by omega))
  have hprice := GeneralPaperSignedDeltaStepPrice.bit_work model.rat model.monotone W m lambda Qv mesh U bid prefixes plan q hm hg hU hbid hcode hpos
  dsimp only [signedWindow,signedProfile,signedRecord]
  dsimp only [queried,found] at hi hr hf
  simp only [List.length_cons,List.length_nil] at hr hcodes hf hind
  omega

end Blotto.GeneralPaperDeltaStepStorage
