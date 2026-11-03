import Blotto.GeneralPaperZeroArrayStorage

/-! Full eight-array local-field initialization and the outer indexed
field-family constructor. Native plans derive all counts; reserved old/new
buffers, frames, full returns, controls and guarded children are included. -/
namespace Blotto.GeneralPaperEpochInitialConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEpochFieldState
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem field_returned {k : ℕ} (model : RationalCostModel) (W m lambda Qv : ℕ) (plan : GeneralPaperEpochFieldPlan.Plan k)
    (hc : GeneralPaperEncodedEpochLevels.Counts (initial plan)) :
    GeneralPaperEncodedEpochLevels.fieldFootprint W (GeneralPaperEpochFieldInitialPrice.run true (fun w => w) model.rat W plan).1≤
      GeneralPaperEncodedEpochLevels.fieldProfile W m lambda k Qv := by
  rw [GeneralPaperEpochFieldInitialPrice.data]
  exact GeneralPaperFieldUpdateConstructionStorage.field_word W m lambda Qv 0 (initial plan) hc (initial_bounded plan)
    (GeneralPaperSparseNodeBits.height_word m lambda k Qv 0 (by omega))

def fieldWindow {k : ℕ} (model : RationalCostModel) (W : ℕ) (plan : GeneralPaperEpochFieldPlan.Plan k) (count : ℕ) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  GeneralPaperZeroArrayStorage.window model W s (min count s) (Nat.min_le_right ..)+
    GeneralPaperZeroArrayStorage.window model W s (min count s) (Nat.min_le_right ..)+
    GeneralPaperZeroArrayStorage.window model W s (min count s) (Nat.min_le_right ..)+
    GeneralPaperZeroArrayStorage.window model W s (min count s) (Nat.min_le_right ..)+
    GeneralPaperZeroArrayStorage.window model W plan.pCells.partition.count (min count plan.pCells.partition.count) (Nat.min_le_right ..)+
    GeneralPaperZeroArrayStorage.window model W plan.qCells.partition.count (min count plan.qCells.partition.count) (Nat.min_le_right ..)+
    GeneralPaperZeroArrayStorage.window model W plan.lambdaCells.partition.count (min count plan.lambdaCells.partition.count) (Nat.min_le_right ..)+
    GeneralPaperZeroArrayStorage.window model W plan.muCells.partition.count (min count plan.muCells.partition.count) (Nat.min_le_right ..)+
    GeneralPaperEncodedEpochLevels.fieldFootprint W (GeneralPaperEpochFieldInitialPrice.run true (fun w => w) model.rat W plan).1+
    fields W [8,s,plan.pCells.partition.count,plan.qCells.partition.count,plan.lambdaCells.partition.count,plan.muCells.partition.count]+256*W

def fieldProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  8*GeneralPaperZeroArrayStorage.profile model W (GeneralPaperBatchCounterPrice.limit k)+
    GeneralPaperEncodedEpochLevels.fieldProfile W m lambda k Qv+
    (6*(natBits (GeneralPaperBatchCounterPrice.limit k+8)+W)+32*W)+256*W

theorem field_bounded {k : ℕ} (model : RationalCostModel) (W m lambda Qv : ℕ) (plan : GeneralPaperEpochFieldPlan.Plan k)
    (hc : GeneralPaperEncodedEpochLevels.Counts (initial plan)) (count : ℕ) :
    fieldWindow model W plan count≤fieldProfile model W m lambda k Qv := by
  let B := GeneralPaperBatchCounterPrice.limit k
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  have hs : s≤B := by unfold s B GeneralPaperBatchCounterPrice.limit; omega
  have hzero : ∀ n≤B, GeneralPaperZeroArrayStorage.window model W n (min count n) (Nat.min_le_right ..)≤GeneralPaperZeroArrayStorage.profile model W B :=
    fun n hn => (GeneralPaperZeroArrayStorage.bounded model W n _ _).trans (GeneralPaperZeroArrayStorage.profile_mono model W n B hn)
  have ho := hzero s hs
  have hp := hzero plan.pCells.partition.count hc.1
  have hq := hzero plan.qCells.partition.count hc.2.1
  have hl := hzero plan.lambdaCells.partition.count hc.2.2.1
  have hm := hzero plan.muCells.partition.count hc.2.2.2
  have hr := field_returned model W m lambda Qv plan hc
  have hi := fields_bound W (natBits (B+8)) [8,s,plan.pCells.partition.count,plan.qCells.partition.count,
    plan.lambdaCells.partition.count,plan.muCells.partition.count] (by
      have hpc := hc.1
      have hqc := hc.2.1
      have hlc := hc.2.2.1
      have hmc := hc.2.2.2
      dsimp only [initial] at hpc hqc hlc hmc
      intro x hx; apply GeneralPaperRankStorageMonotonicity.nat_word
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals omega)
  simp only [List.length_cons,List.length_nil] at hi
  dsimp only [fieldWindow,fieldProfile]
  dsimp only [s,B] at ho hp hq hl hm hi
  omega

theorem cache_field {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : GeneralPaperCatalogueEpochCache.Cache m k)
    (j : Fin m) (count : ℕ) : fieldWindow model W (cache.plans.read j) count≤fieldProfile model W m cache.alphabet.lambda k Qv :=
  field_bounded model W m cache.alphabet.lambda Qv (cache.plans.read j)
    (GeneralPaperEncodedEpochLevels.actual_counts cache (initial (cache.plans.read j)) j rfl) count

def familyPrefix {m k : ℕ} (model : RationalCostModel) (W : ℕ) (cache : GeneralPaperCatalogueEpochCache.Cache m k)
    (count : ℕ) (hc : count≤m) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W m (GeneralPaperEncodedEpochLevels.fieldFootprint W)
    (PaperIndexedArrayConstruction.fill (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m)
      (GeneralPaperEpochInitialFamilyPrice.element true (fun w => w) model.rat W cache) count hc).1

theorem family_prefix {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : GeneralPaperCatalogueEpochCache.Cache m k)
    (count : ℕ) (hc : count≤m) : familyPrefix model W cache count hc≤GeneralPaperEncodedEpochLevels.profile W m cache.alphabet.lambda k Qv := by
  have h := GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m)
    W (GeneralPaperEncodedEpochLevels.fieldProfile W m cache.alphabet.lambda k Qv) (GeneralPaperEncodedEpochLevels.fieldFootprint W)
    (GeneralPaperEpochInitialFamilyPrice.element true (fun w => w) model.rat W cache) (by
      intro j
      exact field_returned model W m cache.alphabet.lambda Qv (cache.plans.read j)
        (GeneralPaperEncodedEpochLevels.actual_counts cache (initial (cache.plans.read j)) j rfl)) count hc
  exact h.trans_eq (by unfold GeneralPaperEncodedEpochLevels.profile; ring)

theorem family_returned {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : GeneralPaperCatalogueEpochCache.Cache m k) :
    GeneralPaperEncodedEpochLevels.familyFootprint W (GeneralPaperEpochInitialFamilyPrice.run true (fun w => w) model.rat W cache).1.fields≤
      GeneralPaperEncodedEpochLevels.profile W m cache.alphabet.lambda k Qv := by
  rw [GeneralPaperEpochInitialFamilyPrice.data]
  apply GeneralPaperEncodedEpochLevels.family_bound
  · intro j
    change GeneralPaperEncodedEpochLevels.Counts ((FixedArrayTable.ofFn (fun i => initial (cache.plans.read i))).read j)
    rw [FixedArrayTable.read_ofFn]
    exact GeneralPaperEncodedEpochLevels.actual_counts cache _ j rfl
  · intro j
    change Bounded ((FixedArrayTable.ofFn (fun i => initial (cache.plans.read i))).read j) _
    rw [FixedArrayTable.read_ofFn]
    exact bounded_mono _ 0 _ (initial_bounded _) (Nat.zero_le _)

def active {m k : ℕ} (model : RationalCostModel) (W : ℕ) (cache : GeneralPaperCatalogueEpochCache.Cache m k) (count innerCount : ℕ) : ℕ :=
  if h : count<m then fieldWindow model W (cache.plans.read ⟨count,h⟩) innerCount+32*W else 0

def familyWindow {m k : ℕ} (model : RationalCostModel) (W : ℕ) (cache : GeneralPaperCatalogueEpochCache.Cache m k)
    (count innerCount : ℕ) (hc : count≤m) : ℕ :=
  2*familyPrefix model W cache count hc+GeneralPaperGridArrayConstructionStorage.frames W m+
    GeneralPaperEncodedEpochLevels.familyFootprint W (GeneralPaperEpochInitialFamilyPrice.run true (fun w => w) model.rat W cache).1.fields+
    active model W cache count innerCount+fields W [m,count,count+1,m+1]+256*W

def familyProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  3*GeneralPaperEncodedEpochLevels.profile W m lambda k Qv+GeneralPaperGridArrayConstructionStorage.frames W m+
    fieldProfile model W m lambda k Qv+(4*(natBits (m+1)+W)+32*W)+288*W

theorem family_bounded {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : GeneralPaperCatalogueEpochCache.Cache m k)
    (count innerCount : ℕ) (hc : count≤m) : familyWindow model W cache count innerCount hc≤familyProfile model W m cache.alphabet.lambda k Qv := by
  have hp := family_prefix model W Qv cache count hc
  have hr := family_returned model W Qv cache
  have ha : active model W cache count innerCount≤fieldProfile model W m cache.alphabet.lambda k Qv+32*W := by
    unfold active
    split
    · exact Nat.add_le_add_right (cache_field model W Qv cache _ innerCount) _
    · exact Nat.zero_le _
  have hi := GeneralPaperMeshPairStorage.index_fields W m [m,count,count+1,m+1] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    all_goals omega)
  simp only [List.length_cons,List.length_nil] at hi
  dsimp only [familyWindow,familyProfile]
  omega

end Blotto.GeneralPaperEpochInitialConstructionStorage
