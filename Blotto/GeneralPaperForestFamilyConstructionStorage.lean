import Blotto.GeneralPaperEpochNodeConstructionStorage

/-! Full native forest-family and four-family construction. Reserved
old/new buffers, complete returns, frames, controls and one guarded node
callback coexist with the incoming forest. Node ownership uses the derived
per-field envelope once, without an instruction-count multiplier. -/
namespace Blotto.GeneralPaperForestFamilyConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOuterLoop GeneralPaperCatalogueOccurrenceHistory GeneralPaperIntervalCache
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def familyPrefix {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) (learner : Learner) (count : ℕ) (hc : count≤m) : ℕ :=
  let shared := prepare a k Qv weights Bc Br
  let trees := treesAt shared a k epoch
  let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
  GeneralPaperEncodedReferenceVector.reservedFootprint W m (GeneralPaperSparseNodeBits.footprint W)
    (PaperIndexedArrayConstruction.fill (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m)
      (GeneralPaperForestUpdateExecution.element true (fun w => w) model.rat W c shared trees state learner) count hc).1

theorem prefix_bounded {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hcache : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) (count : ℕ) (hc : count≤m) :
    familyPrefix model W k Qv a c weights Bc Br epoch learner count hc≤m*(GeneralPaperForestConstructorOperands.nodeProfile W m a.lambda k Qv+W)+64*W :=
  GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m)
    W (GeneralPaperForestConstructorOperands.nodeProfile W m a.lambda k Qv) (GeneralPaperSparseNodeBits.footprint W) _
    (fun j => GeneralPaperForestConstructorOperands.element_bound model W k Qv a c hcache weights Bc Br epoch he learner j) count hc

theorem family_returned {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hcache : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperSparseNodeBits.footprint W)
      (GeneralPaperForestUpdateExecution.family true (fun w => w) model.rat W c shared trees state learner).1≤
      m*(GeneralPaperForestConstructorOperands.nodeProfile W m a.lambda k Qv+W)+32*W := by
  dsimp only
  apply GeneralPaperEncodedFixedVector.bounded
  intro j
  erw [GeneralPaperForestUpdateExecution.family,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact GeneralPaperForestConstructorOperands.element_bound model W k Qv a c hcache weights Bc Br epoch he learner j

def active {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) (learner : Learner) (count remaining : ℕ) : ℕ :=
  if h : count<m then GeneralPaperEpochNodeConstructionStorage.window model W k Qv a c weights Bc Br epoch learner ⟨count,h⟩ remaining else 0

def familyWindow {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ) (learner : Learner) (count remaining : ℕ) (hc : count≤m) : ℕ :=
  let shared := prepare a k Qv weights Bc Br
  let trees := treesAt shared a k epoch
  let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
  2*familyPrefix model W k Qv a c weights Bc Br epoch learner count hc+GeneralPaperGridArrayConstructionStorage.frames W m+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperSparseNodeBits.footprint W)
      (GeneralPaperForestUpdateExecution.family true (fun w => w) model.rat W c shared trees state learner).1+
    active model W k Qv a c weights Bc Br epoch learner count remaining+fields W [m,count,count+1,m+1]+256*W

def familyProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  3*m*(GeneralPaperForestConstructorOperands.nodeProfile W m lambda k Qv+W)+160*W+
    GeneralPaperGridArrayConstructionStorage.frames W m+GeneralPaperEpochNodeConstructionStorage.profile model W m lambda k Qv+
    (4*(natBits (m+1)+W)+32*W)+256*W

theorem family_bounded {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hcache : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (learner : Learner) (count remaining : ℕ) (hc : count≤m) :
    familyWindow model W k Qv a c weights Bc Br epoch learner count remaining hc≤familyProfile model W m a.lambda k Qv := by
  have hp := prefix_bounded model W k Qv a c hcache weights Bc Br epoch he learner count hc
  have hr := family_returned model W k Qv a c hcache weights Bc Br epoch he learner
  have ha : active model W k Qv a c weights Bc Br epoch learner count remaining≤GeneralPaperEpochNodeConstructionStorage.profile model W m a.lambda k Qv := by
    unfold active
    split
    · exact GeneralPaperEpochNodeConstructionStorage.bounded model W k Qv a c hcache weights Bc Br epoch he learner _ remaining
    · exact Nat.zero_le _
  have hi := GeneralPaperMeshPairStorage.index_fields W m [m,count,count+1,m+1] (by
    intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    all_goals omega)
  simp only [List.length_cons,List.length_nil] at hi
  dsimp only [familyWindow,familyProfile] at hr ⊢
  nlinarith only [hp,hr,ha,hi]

def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet) (c : GeneralPaperMaterializedPowerCache.Cache)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count remaining : ℕ) (hc : count≤m) : ℕ :=
  let shared := prepare a k Qv weights Bc Br
  let trees := treesAt shared a k epoch
  let state := GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period
  GeneralPaperEncodedForestStorage.footprint W trees+
    familyWindow model W k Qv a c weights Bc Br epoch .p count remaining hc+
    familyWindow model W k Qv a c weights Bc Br epoch .q count remaining hc+
    familyWindow model W k Qv a c weights Bc Br epoch .lambda count remaining hc+
    familyWindow model W k Qv a c weights Bc Br epoch .mu count remaining hc+
    GeneralPaperEncodedForestStorage.footprint W (GeneralPaperForestUpdateExecution.run true (fun w => w) model.rat W c shared trees state).1+
    fields W [m,a.lambda,a.lambda+1,k]+256*W

def profile (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet) : ℕ :=
  2*GeneralPaperEncodedForestStorage.profile W m a.lambda k Qv+4*familyProfile model W m a.lambda k Qv+
    fields W [m,a.lambda,a.lambda+1,k]+256*W

theorem bounded {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hcache : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count remaining : ℕ) (hc : count≤m)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    window model W k Qv a c weights Bc Br epoch count remaining hc≤profile model W m k Qv a := by
  have ho := GeneralPaperEncodedForestStorage.actual W k Qv a weights Bc Br epoch (by omega)
  have hp := family_bounded model W k Qv a c hcache weights Bc Br epoch he .p count remaining hc
  have hq := family_bounded model W k Qv a c hcache weights Bc Br epoch he .q count remaining hc
  have hl := family_bounded model W k Qv a c hcache weights Bc Br epoch he .lambda count remaining hc
  have hm := family_bounded model W k Qv a c hcache weights Bc Br epoch he .mu count remaining hc
  have hr := GeneralPaperForestConstructorOperands.returned model W k Qv a c hcache weights Bc Br epoch he
  dsimp only [window,profile] at hr ⊢
  omega

end Blotto.GeneralPaperForestFamilyConstructionStorage
