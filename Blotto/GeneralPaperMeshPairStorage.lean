import Blotto.GeneralPaperCachedMeshQueryStorage

/-! Native CDF/tail pairs and the four-count caller retain their full
records, child results, partial/final work additions, index controls and
primitive scratch. Prefix/rank arrays are borrowed from the epoch cache. -/
namespace Blotto.GeneralPaperMeshPairStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshPrefixInvariant (Good)
open GeneralPaperMeshPairExecution
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem count_word (m lambda k Qv mesh x : ℕ)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hx : x≤mesh) :
    natBits x≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hw := GeneralPaperMeshQueryEnvelope.mesh_word m lambda k Qv
  rw [←hm] at hw
  exact (Nat.add_le_add_left (binaryWordWidth_mono hx) 1).trans hw

theorem metadata_fields (W m lambda k Qv : ℕ) (xs : List ℕ)
    (hx : ∀ x∈xs,x≤GeneralPaperMeshQueryMetadata.cap k) :
    fields W xs≤xs.length*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+32*W := by
  apply fields_bound
  intro x hmem
  exact (Nat.add_le_add_left (binaryWordWidth_mono (hx x hmem)) 1).trans
    (GeneralPaperMeshQueryMetadata.operand_word m lambda k Qv)

theorem index_fields (W n : ℕ) (xs : List ℕ) (hx : ∀ x∈xs,x≤n+1) :
    fields W xs≤xs.length*(natBits (n+1)+W)+32*W := by
  apply fields_bound
  intro x hmem
  exact Nat.add_le_add_left (binaryWordWidth_mono (hx x hmem)) 1

def cdfWindow {n k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperCDFPairPlan.Plan k n) (q : Fin n) : ℕ :=
  let lower := GeneralPaperCachedMeshPrefixQuery.cached true model.rat W mesh prefixes plan.lower q
  let upper := GeneralPaperCachedMeshPrefixQuery.cached true model.rat W mesh prefixes plan.upper q
  let found := cdf true model.rat W mesh prefixes plan q
  GeneralPaperCachedMeshQueryStorage.prefixWindow model W mesh prefixes plan.lower q+
    GeneralPaperCachedMeshQueryStorage.prefixWindow model W mesh prefixes plan.upper q+
    fields W [found.1.lower,found.1.upper,found.1.work]+fields W [n,q.val]+
    fields W [lower.1.work,upper.1.work,lower.1.work+upper.1.work,8]+found.2+256*W

def cdfProfile (model : RationalCostModel) (W m lambda k Qv n : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  2*GeneralPaperCachedMeshQueryStorage.prefixProfile model W m lambda k Qv n+
    (3*(H+W)+32*W)+(2*(natBits (n+1)+W)+32*W)+(4*(H+W)+32*W)+
    GeneralPaperMeshPairPrice.cdfProfile model.rat W m lambda k Qv+256*W

theorem cdf_bounded {n k : ℕ} (model : RationalCostModel) (W m lambda Qv mesh : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperCDFPairPlan.Plan k n) (q : Fin n)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hg : Good m lambda k Qv prefixes) :
    cdfWindow model W mesh prefixes plan q≤cdfProfile model W m lambda k Qv n := by
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let lower := GeneralPaperCachedMeshPrefixQuery.cached true model.rat W mesh prefixes plan.lower q
  let upper := GeneralPaperCachedMeshPrefixQuery.cached true model.rat W mesh prefixes plan.upper q
  let found := cdf true model.rat W mesh prefixes plan q
  have hl := GeneralPaperCachedMeshQueryStorage.prefix_bounded model W m lambda Qv mesh prefixes plan.lower q hm hg
  have hu := GeneralPaperCachedMeshQueryStorage.prefix_bounded model W m lambda Qv mesh prefixes plan.upper q hm hg
  have hlow : natBits found.1.lower≤H := count_word m lambda k Qv mesh _ hm
    (GeneralPaperMeshCountBounds.cached_prefix_bound true model.rat W m lambda Qv mesh prefixes plan.lower q hm hg)
  have hupp : natBits found.1.upper≤H := count_word m lambda k Qv mesh _ hm
    (GeneralPaperMeshCountBounds.cached_prefix_bound true model.rat W m lambda Qv mesh prefixes plan.upper q hm hg)
  have hlw : lower.1.work=12*(30+k)+42 := by
    rw [GeneralPaperCachedMeshPrefixQuery.cached_data true model.rat W mesh prefixes plan.lower q hm,GeneralPaperRankedCDFQuery.cached_work]
  have huw : upper.1.work=12*(30+k)+42 := by
    rw [GeneralPaperCachedMeshPrefixQuery.cached_data true model.rat W mesh prefixes plan.upper q hm,GeneralPaperRankedCDFQuery.cached_work]
  have hwork : found.1.work≤GeneralPaperMeshQueryMetadata.cap k := by
    change lower.1.work+upper.1.work+8≤_
    rw [hlw,huw]
    unfold GeneralPaperMeshQueryMetadata.cap
    omega
  have hww : natBits found.1.work≤H := (Nat.add_le_add_left (binaryWordWidth_mono hwork) 1).trans
    (GeneralPaperMeshQueryMetadata.operand_word m lambda k Qv)
  have hr := fields_bound W H [found.1.lower,found.1.upper,found.1.work] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact hlow
    · exact hupp
    · exact hww)
  have hi := index_fields W n [n,q.val] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · omega
    · exact q.isLt.le.trans (by omega))
  have hc := metadata_fields W m lambda k Qv [lower.1.work,upper.1.work,lower.1.work+upper.1.work,8] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    all_goals (unfold GeneralPaperMeshQueryMetadata.cap; omega))
  have hp := GeneralPaperMeshPairPrice.cdf_bit_work model.rat model.monotone W m lambda Qv mesh prefixes plan q hm hg
  dsimp only [cdfWindow,cdfProfile]
  dsimp only [lower,upper,found] at hr hc
  simp only [List.length_cons,List.length_nil] at hr hi hc
  omega

def tailsWindow {n k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperSignedTailPlan.Plan k n) (q : Fin n) : ℕ :=
  let positive := GeneralPaperCachedMeshIntervalQuery.cached true model.rat W mesh prefixes plan.positive q.castSucc (Fin.last n)
  let negative := GeneralPaperCachedMeshIntervalQuery.cached true model.rat W mesh prefixes plan.negative q.castSucc (Fin.last n)
  let found := tails true model.rat W mesh prefixes plan q
  GeneralPaperCachedMeshQueryStorage.intervalWindow model W mesh prefixes plan.positive q.castSucc (Fin.last n)+
    GeneralPaperCachedMeshQueryStorage.intervalWindow model W mesh prefixes plan.negative q.castSucc (Fin.last n)+
    fields W [found.1.positive,found.1.negative,found.1.work]+fields W [n,n+1,q.val,n]+
    fields W [positive.1.work,negative.1.work,positive.1.work+negative.1.work,8]+found.2+256*W

def tailsProfile (model : RationalCostModel) (W m lambda k Qv n : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  2*GeneralPaperCachedMeshQueryStorage.intervalProfile model W m lambda k Qv (n+1)+
    (3*(H+W)+32*W)+(4*(natBits (n+1)+W)+32*W)+(4*(H+W)+32*W)+
    GeneralPaperMeshPairPrice.tailsProfile model.rat W m lambda k Qv+256*W

theorem tails_bounded {n k : ℕ} (model : RationalCostModel) (W m lambda Qv mesh : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperSignedTailPlan.Plan k n) (q : Fin n)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hg : Good m lambda k Qv prefixes) :
    tailsWindow model W mesh prefixes plan q≤tailsProfile model W m lambda k Qv n := by
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let positive := GeneralPaperCachedMeshIntervalQuery.cached true model.rat W mesh prefixes plan.positive q.castSucc (Fin.last n)
  let negative := GeneralPaperCachedMeshIntervalQuery.cached true model.rat W mesh prefixes plan.negative q.castSucc (Fin.last n)
  let found := tails true model.rat W mesh prefixes plan q
  have hpw := GeneralPaperCachedMeshQueryStorage.interval_bounded model W m lambda Qv mesh prefixes plan.positive q.castSucc (Fin.last n) hm hg
  have hnw := GeneralPaperCachedMeshQueryStorage.interval_bounded model W m lambda Qv mesh prefixes plan.negative q.castSucc (Fin.last n) hm hg
  have hpos : natBits found.1.positive≤H := count_word m lambda k Qv mesh _ hm
    (GeneralPaperMeshCountBounds.cached_interval_bound true model.rat W m lambda Qv mesh prefixes plan.positive q.castSucc (Fin.last n) hm hg)
  have hneg : natBits found.1.negative≤H := count_word m lambda k Qv mesh _ hm
    (GeneralPaperMeshCountBounds.cached_interval_bound true model.rat W m lambda Qv mesh prefixes plan.negative q.castSucc (Fin.last n) hm hg)
  have hpww : positive.1.work=12*(30+k)+58 := by
    rw [GeneralPaperCachedMeshIntervalQuery.cached_data true model.rat W mesh prefixes plan.positive q.castSucc (Fin.last n) hm,GeneralPaperIntervalQuery.cached_work]
  have hnww : negative.1.work=12*(30+k)+58 := by
    rw [GeneralPaperCachedMeshIntervalQuery.cached_data true model.rat W mesh prefixes plan.negative q.castSucc (Fin.last n) hm,GeneralPaperIntervalQuery.cached_work]
  have hwork : found.1.work≤GeneralPaperMeshQueryMetadata.cap k := by
    change positive.1.work+negative.1.work+8≤_
    rw [hpww,hnww]
    unfold GeneralPaperMeshQueryMetadata.cap
    omega
  have hww : natBits found.1.work≤H := (Nat.add_le_add_left (binaryWordWidth_mono hwork) 1).trans
    (GeneralPaperMeshQueryMetadata.operand_word m lambda k Qv)
  have hr := fields_bound W H [found.1.positive,found.1.negative,found.1.work] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact hpos
    · exact hneg
    · exact hww)
  have hi := index_fields W n [n,n+1,q.val,n] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    all_goals omega)
  have hc := metadata_fields W m lambda k Qv [positive.1.work,negative.1.work,positive.1.work+negative.1.work,8] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    all_goals (unfold GeneralPaperMeshQueryMetadata.cap; omega))
  have hp := GeneralPaperMeshPairPrice.tails_bit_work model.rat model.monotone W m lambda Qv mesh prefixes plan q hm hg
  dsimp only [tailsWindow,tailsProfile]
  dsimp only [positive,negative,found] at hr hc
  simp only [List.length_cons,List.length_nil] at hr hi hc
  omega

def countsWindow {n k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (cdfPrefix tailPrefix : Prefix k)
    (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n) : ℕ :=
  let cp := cdf true model.rat W mesh cdfPrefix plan.cdf q
  let tp := tails true model.rat W mesh tailPrefix plan.tails q
  let found := counts true model.rat W mesh cdfPrefix tailPrefix plan q
  cdfWindow model W mesh cdfPrefix plan.cdf q+tailsWindow model W mesh tailPrefix plan.tails q+
    fields W [found.1.lower,found.1.upper,found.1.positive,found.1.negative,found.1.work]+
    fields W [n,q.val]+fields W [cp.1.work,tp.1.work,cp.1.work+tp.1.work,16]+found.2+256*W

def countsProfile (model : RationalCostModel) (W m lambda k Qv n : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  cdfProfile model W m lambda k Qv n+tailsProfile model W m lambda k Qv n+
    (5*(H+W)+32*W)+(2*(natBits (n+1)+W)+32*W)+(4*(H+W)+32*W)+
    GeneralPaperMeshPairPrice.countsProfile model.rat W m lambda k Qv+256*W

theorem counts_bounded {n k : ℕ} (model : RationalCostModel) (W m lambda Qv mesh : ℕ) (cdfPrefix tailPrefix : Prefix k)
    (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hcdf : Good m lambda k Qv cdfPrefix) (htail : Good m lambda k Qv tailPrefix) :
    countsWindow model W mesh cdfPrefix tailPrefix plan q≤countsProfile model W m lambda k Qv n := by
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let cp := cdf true model.rat W mesh cdfPrefix plan.cdf q
  let tp := tails true model.rat W mesh tailPrefix plan.tails q
  let found := counts true model.rat W mesh cdfPrefix tailPrefix plan q
  have hc := cdf_bounded model W m lambda Qv mesh cdfPrefix plan.cdf q hm hcdf
  have ht := tails_bounded model W m lambda Qv mesh tailPrefix plan.tails q hm htail
  have hb := GeneralPaperMeshCountBounds.counts_bound true model.rat W m lambda Qv mesh cdfPrefix tailPrefix plan q hm hcdf htail
  have hl : natBits found.1.lower≤H := count_word m lambda k Qv mesh _ hm (by rw [hm]; exact hb.1)
  have hu : natBits found.1.upper≤H := count_word m lambda k Qv mesh _ hm (by rw [hm]; exact hb.2.1)
  have hp : natBits found.1.positive≤H := count_word m lambda k Qv mesh _ hm (by rw [hm]; exact hb.2.2.1)
  have hn : natBits found.1.negative≤H := count_word m lambda k Qv mesh _ hm (by rw [hm]; exact hb.2.2.2)
  have hcw : cp.1.work=24*(30+k)+92 := by
    rw [GeneralPaperMeshPairExecution.cdf_data true model.rat W mesh cdfPrefix plan.cdf q hm,GeneralPaperCDFPairPlan.evaluate_work]
  have htw : tp.1.work=24*(30+k)+124 := by
    rw [GeneralPaperMeshPairExecution.tails_data true model.rat W mesh tailPrefix plan.tails q hm,GeneralPaperSignedTailPlan.evaluate_work]
  have hwork : found.1.work≤GeneralPaperMeshQueryMetadata.cap k := by
    change cp.1.work+tp.1.work+16≤_
    rw [hcw,htw]
    unfold GeneralPaperMeshQueryMetadata.cap
    omega
  have hww : natBits found.1.work≤H := (Nat.add_le_add_left (binaryWordWidth_mono hwork) 1).trans
    (GeneralPaperMeshQueryMetadata.operand_word m lambda k Qv)
  have hr := fields_bound W H [found.1.lower,found.1.upper,found.1.positive,found.1.negative,found.1.work] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl
    · exact hl
    · exact hu
    · exact hp
    · exact hn
    · exact hww)
  have hi := index_fields W n [n,q.val] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · omega
    · exact q.isLt.le.trans (by omega))
  have hmdata := metadata_fields W m lambda k Qv [cp.1.work,tp.1.work,cp.1.work+tp.1.work,16] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    all_goals (unfold GeneralPaperMeshQueryMetadata.cap; omega))
  have hprice := GeneralPaperMeshPairPrice.counts_bit_work model.rat model.monotone W m lambda Qv mesh cdfPrefix tailPrefix plan q hm hcdf htail
  dsimp only [countsWindow,countsProfile]
  dsimp only [cp,tp,found] at hr hmdata
  simp only [List.length_cons,List.length_nil] at hr hi hmdata
  omega

end Blotto.GeneralPaperMeshPairStorage
