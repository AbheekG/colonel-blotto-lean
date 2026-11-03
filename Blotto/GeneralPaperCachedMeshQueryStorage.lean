import Blotto.GeneralPaperMeshQueryStorage

/-! Cached mesh point/interval wrappers retain every result and work
field, actual rank/index controls, prefix reads and interval difference.
Owned arrays stay in the source resident ledger; this counts borrowed cursors.
The actual native query-array size remains explicit until its caller joins it. -/
namespace Blotto.GeneralPaperCachedMeshQueryStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshPrefixInvariant (Good)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def controlWord (m lambda k Qv n : ℕ) : ℕ := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+
  natBits ((GeneralPaperSourceParameters.prepare k).summarySize+1)+natBits (n+1)

def prefixControls {n k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (prefixes : Prefix k)
    (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (q : Fin n) : ℕ :=
  let rank := ranks.read q
  let total := prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize)
  let raw := GeneralPaperMeshQueryExecution.selected model.rat W k mesh (prefixes.read rank) total
  let found := GeneralPaperCachedMeshPrefixQuery.run true model.rat W mesh prefixes rank
  let cached := GeneralPaperCachedMeshPrefixQuery.cached true model.rat W mesh prefixes ranks q
  fields W [mesh,n,q.val,rank.val,(GeneralPaperSourceParameters.prepare k).summarySize,
    (GeneralPaperSourceParameters.prepare k).summarySize+1,prefixes.read rank,total,raw.1.work,found.1.work,cached.1.work]

def prefixWindow {n k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (prefixes : Prefix k)
    (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (q : Fin n) : ℕ :=
  GeneralPaperMeshQueryStorage.window model W k mesh (prefixes.read (ranks.read q))
      (prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize))+
    GeneralPaperQuotientConstructionStorage.record W (GeneralPaperCachedMeshPrefixQuery.run true model.rat W mesh prefixes (ranks.read q)).1+
    GeneralPaperQuotientConstructionStorage.record W (GeneralPaperCachedMeshPrefixQuery.cached true model.rat W mesh prefixes ranks q).1+
    prefixControls model W mesh prefixes ranks q+(GeneralPaperCachedMeshPrefixQuery.cached true model.rat W mesh prefixes ranks q).2+256*W

def prefixProfile (model : RationalCostModel) (W m lambda k Qv n : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  GeneralPaperMeshQueryStorage.profile model W m lambda k Qv+2*(GeneralPaperMeshQueryStorage.recordProfile W m lambda k Qv+H)+
    11*(controlWord m lambda k Qv n+W)+32*W+GeneralPaperCachedMeshPrefixQuery.cachedProfile model.rat W m lambda k Qv+256*W

theorem prefix_bounded {n k : ℕ} (model : RationalCostModel) (W m lambda Qv mesh : ℕ) (prefixes : Prefix k)
    (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (q : Fin n)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hg : Good m lambda k Qv prefixes) :
    prefixWindow model W mesh prefixes ranks q≤prefixProfile model W m lambda k Qv n := by
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let rank := ranks.read q
  let total := prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize)
  let raw := GeneralPaperMeshQueryExecution.selected model.rat W k mesh (prefixes.read rank) total
  let found := GeneralPaperCachedMeshPrefixQuery.run true model.rat W mesh prefixes rank
  let cached := GeneralPaperCachedMeshPrefixQuery.cached true model.rat W mesh prefixes ranks q
  have hcore := GeneralPaperMeshQueryStorage.bounded model W m lambda k Qv mesh (prefixes.read rank) total hm hg.1 (hg.2.1 rank) hg.2.2
  have hraw := GeneralPaperMeshQueryStorage.returned model W m lambda k Qv mesh (prefixes.read rank) total hm hg.1 (hg.2.1 rank) hg.2.2
  have hw0 := GeneralPaperMeshQueryStorage.work_word model W m lambda k Qv mesh (prefixes.read rank) total 0 hm (by omega)
  simp only [Nat.add_zero] at hw0
  change natBits raw.1.work≤H at hw0
  have hw1 : natBits found.1.work≤H := by
    have h := GeneralPaperMeshQueryStorage.work_word model W m lambda k Qv mesh (prefixes.read rank) total 16 hm (by omega)
    exact h
  have hw2 : natBits cached.1.work≤H := by
    rw [GeneralPaperCachedMeshPrefixQuery.cached_data true model.rat W mesh prefixes ranks q hm,GeneralPaperRankedCDFQuery.cached_work]
    exact (Nat.add_le_add_left (binaryWordWidth_mono (show 12*(30+k)+42≤GeneralPaperMeshQueryMetadata.cap k by
      unfold GeneralPaperMeshQueryMetadata.cap; omega)) 1).trans (GeneralPaperMeshQueryMetadata.operand_word m lambda k Qv)
  have hr1 := (GeneralPaperMeshQueryStorage.record_changed W H raw.1 found.1 rfl rfl hw1).trans (Nat.add_le_add_right hraw H)
  have hr2 := (GeneralPaperMeshQueryStorage.record_changed W H raw.1 cached.1 rfl rfl hw2).trans (Nat.add_le_add_right hraw H)
  have hmesh := GeneralPaperMeshQueryEnvelope.mesh_word m lambda k Qv
  rw [←hm] at hmesh
  change natBits mesh≤H at hmesh
  have hread := GeneralPaperMeshPrefixInvariant.prefix_word m lambda k Qv prefixes hg rank
  change natBits (prefixes.read rank)≤H at hread
  have htotal : natBits total≤H := hg.2.2
  have hn : natBits n≤natBits (n+1) := Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
  have hq : natBits q.val≤natBits (n+1) := Nat.add_le_add_left (binaryWordWidth_mono (by have := q.isLt; omega)) 1
  have hrank : natBits rank.val≤natBits ((GeneralPaperSourceParameters.prepare k).summarySize+1) :=
    Nat.add_le_add_left (binaryWordWidth_mono rank.isLt.le) 1
  have hsize : natBits (GeneralPaperSourceParameters.prepare k).summarySize≤natBits ((GeneralPaperSourceParameters.prepare k).summarySize+1) :=
    Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
  have hf := fields_bound W (controlWord m lambda k Qv n)
    [mesh,n,q.val,rank.val,(GeneralPaperSourceParameters.prepare k).summarySize,(GeneralPaperSourceParameters.prepare k).summarySize+1,
      prefixes.read rank,total,raw.1.work,found.1.work,cached.1.work] (by
        intro x hx
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals (dsimp only [controlWord]; change _≤H+_+_; omega))
  change prefixControls model W mesh prefixes ranks q≤11*(controlWord m lambda k Qv n+W)+32*W at hf
  have hp := GeneralPaperCachedMeshPrefixQuery.cached_bit_work model.rat model.monotone W m lambda Qv mesh prefixes ranks q hm hg
  dsimp only [prefixWindow,prefixProfile]
  dsimp only [raw,found,cached,rank,total] at hcore hr1 hr2
  omega

def intervalControls {n k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (prefixes : Prefix k)
    (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (lo hi : Fin n) : ℕ :=
  let low := prefixes.read (ranks.read lo)
  let high := prefixes.read (ranks.read hi)
  let total := prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize)
  let raw := GeneralPaperMeshQueryExecution.selected model.rat W k mesh (high-low) total
  let found := GeneralPaperCachedMeshIntervalQuery.run true model.rat W mesh prefixes (ranks.read lo) (ranks.read hi)
  let cached := GeneralPaperCachedMeshIntervalQuery.cached true model.rat W mesh prefixes ranks lo hi
  fields W [mesh,n,lo.val,hi.val,(ranks.read lo).val,(ranks.read hi).val,
    (GeneralPaperSourceParameters.prepare k).summarySize,(GeneralPaperSourceParameters.prepare k).summarySize+1,
    high,low,high-low,total,raw.1.work,found.1.work,cached.1.work]

def intervalWindow {n k : ℕ} (model : RationalCostModel) (W mesh : ℕ) (prefixes : Prefix k)
    (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (lo hi : Fin n) : ℕ :=
  GeneralPaperMeshQueryStorage.window model W k mesh (prefixes.read (ranks.read hi)-prefixes.read (ranks.read lo))
      (prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize))+
    GeneralPaperQuotientConstructionStorage.record W (GeneralPaperCachedMeshIntervalQuery.run true model.rat W mesh prefixes (ranks.read lo) (ranks.read hi)).1+
    GeneralPaperQuotientConstructionStorage.record W (GeneralPaperCachedMeshIntervalQuery.cached true model.rat W mesh prefixes ranks lo hi).1+
    intervalControls model W mesh prefixes ranks lo hi+(GeneralPaperCachedMeshIntervalQuery.cached true model.rat W mesh prefixes ranks lo hi).2+256*W

def intervalProfile (model : RationalCostModel) (W m lambda k Qv n : ℕ) : ℕ :=
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  GeneralPaperMeshQueryStorage.profile model W m lambda k Qv+2*(GeneralPaperMeshQueryStorage.recordProfile W m lambda k Qv+H)+
    15*(controlWord m lambda k Qv n+W)+32*W+GeneralPaperCachedMeshIntervalQuery.cachedProfile model.rat W m lambda k Qv+256*W

theorem interval_bounded {n k : ℕ} (model : RationalCostModel) (W m lambda Qv mesh : ℕ) (prefixes : Prefix k)
    (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (lo hi : Fin n)
    (hm : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hg : Good m lambda k Qv prefixes) :
    intervalWindow model W mesh prefixes ranks lo hi≤ intervalProfile model W m lambda k Qv n := by
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
  let low := prefixes.read (ranks.read lo)
  let high := prefixes.read (ranks.read hi)
  let total := prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize)
  let raw := GeneralPaperMeshQueryExecution.selected model.rat W k mesh (high-low) total
  let found := GeneralPaperCachedMeshIntervalQuery.run true model.rat W mesh prefixes (ranks.read lo) (ranks.read hi)
  let cached := GeneralPaperCachedMeshIntervalQuery.cached true model.rat W mesh prefixes ranks lo hi
  have hnum : high-low≤total := (Nat.sub_le _ _).trans (hg.2.1 _)
  have hcore := GeneralPaperMeshQueryStorage.bounded model W m lambda k Qv mesh (high-low) total hm hg.1 hnum hg.2.2
  have hraw := GeneralPaperMeshQueryStorage.returned model W m lambda k Qv mesh (high-low) total hm hg.1 hnum hg.2.2
  have hw0 := GeneralPaperMeshQueryStorage.work_word model W m lambda k Qv mesh (high-low) total 0 hm (by omega)
  simp only [Nat.add_zero] at hw0
  change natBits raw.1.work≤H at hw0
  have hw1 : natBits found.1.work≤H := GeneralPaperMeshQueryStorage.work_word model W m lambda k Qv mesh (high-low) total 24 hm (by omega)
  have hw2 : natBits cached.1.work≤H := by
    rw [GeneralPaperCachedMeshIntervalQuery.cached_data true model.rat W mesh prefixes ranks lo hi hm,GeneralPaperIntervalQuery.cached_work]
    exact (Nat.add_le_add_left (binaryWordWidth_mono (show 12*(30+k)+58≤GeneralPaperMeshQueryMetadata.cap k by
      unfold GeneralPaperMeshQueryMetadata.cap; omega)) 1).trans (GeneralPaperMeshQueryMetadata.operand_word m lambda k Qv)
  have hr1 := (GeneralPaperMeshQueryStorage.record_changed W H raw.1 found.1 rfl rfl hw1).trans (Nat.add_le_add_right hraw H)
  have hr2 := (GeneralPaperMeshQueryStorage.record_changed W H raw.1 cached.1 rfl rfl hw2).trans (Nat.add_le_add_right hraw H)
  have hmesh := GeneralPaperMeshQueryEnvelope.mesh_word m lambda k Qv
  rw [←hm] at hmesh
  change natBits mesh≤H at hmesh
  have hhigh := GeneralPaperMeshPrefixInvariant.prefix_word m lambda k Qv prefixes hg (ranks.read hi)
  have hlow := GeneralPaperMeshPrefixInvariant.prefix_word m lambda k Qv prefixes hg (ranks.read lo)
  have hdiff := (Nat.add_le_add_left (binaryWordWidth_mono hnum) 1).trans hg.2.2
  change natBits high≤H at hhigh
  change natBits low≤H at hlow
  change natBits (high-low)≤H at hdiff
  have htotal : natBits total≤H := hg.2.2
  have hn : natBits n≤natBits (n+1) := Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
  have hlo : natBits lo.val≤natBits (n+1) := Nat.add_le_add_left (binaryWordWidth_mono (by have := lo.isLt; omega)) 1
  have hhi : natBits hi.val≤natBits (n+1) := Nat.add_le_add_left (binaryWordWidth_mono (by have := hi.isLt; omega)) 1
  have hrlo : natBits (ranks.read lo).val≤natBits ((GeneralPaperSourceParameters.prepare k).summarySize+1) := Nat.add_le_add_left (binaryWordWidth_mono (ranks.read lo).isLt.le) 1
  have hrhi : natBits (ranks.read hi).val≤natBits ((GeneralPaperSourceParameters.prepare k).summarySize+1) := Nat.add_le_add_left (binaryWordWidth_mono (ranks.read hi).isLt.le) 1
  have hsize : natBits (GeneralPaperSourceParameters.prepare k).summarySize≤natBits ((GeneralPaperSourceParameters.prepare k).summarySize+1) := Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
  have hf := fields_bound W (controlWord m lambda k Qv n)
    [mesh,n,lo.val,hi.val,(ranks.read lo).val,(ranks.read hi).val,(GeneralPaperSourceParameters.prepare k).summarySize,
      (GeneralPaperSourceParameters.prepare k).summarySize+1,high,low,high-low,total,raw.1.work,found.1.work,cached.1.work] (by
        intro x hx
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals (dsimp only [controlWord]; change _≤H+_+_; omega))
  change intervalControls model W mesh prefixes ranks lo hi≤15*(controlWord m lambda k Qv n+W)+32*W at hf
  have hp := GeneralPaperCachedMeshIntervalQuery.cached_bit_work model.rat model.monotone W m lambda Qv mesh prefixes ranks lo hi hm hg
  dsimp only [intervalWindow,intervalProfile]
  dsimp only [raw,found,cached,low,high,total] at hcore hr1 hr2
  omega

end Blotto.GeneralPaperCachedMeshQueryStorage
