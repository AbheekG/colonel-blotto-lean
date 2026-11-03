import Blotto.GeneralPaperSnapshotConstructionStorage

/-! Native all-field snapshot fill. The incoming state, both reserved
prefix buffers, full returned family, structural frames and one guarded
four-block child coexist. Finished and empty families select no child. -/
namespace Blotto.GeneralPaperSnapshotFamilyConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperAdaptiveEpoch GeneralPaperEpochFieldState
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def filled {m k : ℕ} (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (states : Fields m k) (count : ℕ) (hc : count≤m) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W m (GeneralPaperEncodedSnapshotStorage.fieldFootprint W)
    (PaperIndexedArrayConstruction.fill (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m)
      (GeneralPaperEpochSnapshotFamilyPrice.element true (fun w => w) model.rat W c states) count hc).1

theorem filled_bound {m k : ℕ} (model : RationalCostModel) (W lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (states : Fields m k)
    (hb : ∀ j,Bounded (states.read j) c.controls.precision.levelBound) (count : ℕ) (ht : count≤m) :
    filled model W c states count ht≤m*(GeneralPaperEncodedSnapshotStorage.fieldProfile W m lambda k Qv+W)+64*W :=
  GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m)
    W (GeneralPaperEncodedSnapshotStorage.fieldProfile W m lambda k Qv) (GeneralPaperEncodedSnapshotStorage.fieldFootprint W)
    (GeneralPaperEpochSnapshotFamilyPrice.element true (fun w => w) model.rat W c states)
    (fun j => GeneralPaperSnapshotConstructionStorage.field_returned model W m lambda Qv c hc (states.read j) (hb j)) count ht

theorem returned {m k : ℕ} (model : RationalCostModel) (W lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (states : Fields m k)
    (hb : ∀ j,Bounded (states.read j) c.controls.precision.levelBound) :
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedSnapshotStorage.fieldFootprint W)
      (GeneralPaperEpochSnapshotFamilyPrice.run true (fun w => w) model.rat W c states).1≤
      m*(GeneralPaperEncodedSnapshotStorage.fieldProfile W m lambda k Qv+W)+32*W := by
  apply GeneralPaperEncodedFixedVector.bounded
  intro j
  rw [GeneralPaperEpochSnapshotFamilyPrice.run,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact GeneralPaperSnapshotConstructionStorage.field_returned model W m lambda Qv c hc (states.read j) (hb j)

def active {m k : ℕ} (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (states : Fields m k) (count innerCount used copied : ℕ)
    (hi : innerCount≤(GeneralPaperSourceParameters.prepare k).summarySize) : ℕ :=
  if h : count<m then GeneralPaperSnapshotConstructionStorage.fieldWindow model W c (states.read ⟨count,h⟩) innerCount used copied hi+32*W else 0

theorem active_finished {m k : ℕ} (model : RationalCostModel) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (states : Fields m k) (count innerCount used copied : ℕ)
    (hi : innerCount≤(GeneralPaperSourceParameters.prepare k).summarySize) (hc : m≤count) :
    active model W c states count innerCount used copied hi=0 := by
  simp only [active,dite_eq_right (Nat.not_lt.mpr hc)]

def window {m k : ℕ} (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (states : Fields m k) (count innerCount used copied : ℕ) (ht : count≤m)
    (hi : innerCount≤(GeneralPaperSourceParameters.prepare k).summarySize) : ℕ :=
  GeneralPaperEncodedEpochLevels.familyFootprint W states+2*filled model W c states count ht+
    GeneralPaperGridArrayConstructionStorage.frames W m+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedSnapshotStorage.fieldFootprint W)
      (GeneralPaperEpochSnapshotFamilyPrice.run true (fun w => w) model.rat W c states).1+
    active model W c states count innerCount used copied hi+fields W [m,count,count+1,m+1]+256*W

def profile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperEncodedEpochLevels.profile W m lambda k Qv+
    3*m*(GeneralPaperEncodedSnapshotStorage.fieldProfile W m lambda k Qv+W)+160*W+
    GeneralPaperGridArrayConstructionStorage.frames W m+
    GeneralPaperSnapshotConstructionStorage.fieldProfile model W m lambda k Qv+32*W+
    4*(natBits (m+1)+W)+288*W

theorem bounded {m k : ℕ} (model : RationalCostModel) (W lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv) (states : Fields m k)
    (hb : ∀ j,Bounded (states.read j) c.controls.precision.levelBound)
    (hn : ∀ j,GeneralPaperEncodedEpochLevels.Counts (states.read j)) (count innerCount used copied : ℕ)
    (ht : count≤m) (hi : innerCount≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    window model W c states count innerCount used copied ht hi≤profile model W m lambda k Qv := by
  have hp := filled_bound model W lambda Qv c hc states hb count ht
  have hr := returned model W lambda Qv c hc states hb
  have hG : c.controls.precision.levelBound=GeneralPaperPowerPrecision.levelBound lambda k := by rw [hc]; rfl
  have hb' := hb
  rw [hG] at hb'
  have hs := GeneralPaperEncodedEpochLevels.family_bound W lambda Qv states hn hb'
  have ha : active model W c states count innerCount used copied hi≤
      GeneralPaperSnapshotConstructionStorage.fieldProfile model W m lambda k Qv+32*W := by
    unfold active
    split
    · exact Nat.add_le_add_right
        (GeneralPaperSnapshotConstructionStorage.field_bound model W m lambda Qv c hc _ (hb _) (hn _) innerCount used copied hi) _
    · exact Nat.zero_le _
  have hf := fields_bound W (natBits (m+1)) [m,count,count+1,m+1] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx|hx|hx|hx <;> rw [hx] <;>
      exact Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1)
  change _≤4*(natBits (m+1)+W)+32*W at hf
  dsimp only [window,profile]
  nlinarith only [hp,hr,hs,ha,hf]

end Blotto.GeneralPaperSnapshotFamilyConstructionStorage
