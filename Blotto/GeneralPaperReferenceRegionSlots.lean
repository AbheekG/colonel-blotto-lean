import Blotto.GeneralPaperEqualDominantLayoutAccess

/-! A complete reference-bearing header belongs to one actual layout region.
All its slots are packed after its fixed prefix; linked head/tail cells can
be interleaved in this packed target sequence. Validity and capacity are
proof premises, not construction inputs. Every written key lies in its owner. -/
namespace Blotto.GeneralPaperReferenceRegionSlots
open GeneralPaperSequentialLayout GeneralPaperReferenceSlotConstruction
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

structure Header (A : ℕ) where
  region : Region A
  fixed : ℕ
  targets : List (FixedBinaryWord A)

def Valid {A : ℕ} (header : Header A) : Prop := A * (header.fixed + header.targets.length) ≤ header.region.length

def batch (model : RationalCostModel) (S A : ℕ) (header : Header A) : GeneralPaperReferenceSlotBatch.Result A :=
  GeneralPaperReferenceSlotBatch.run model S A header.region.start header.fixed 1 0 0 header.targets

theorem capacity {A : ℕ} (header : Header A) (hValid : Valid header) (hCap : header.region.stop < 2 ^ A) :
    header.region.start + A * (header.fixed + 1 * header.targets.length) < 2 ^ A := by
  unfold Valid Region.stop at *
  simp only [one_mul]
  omega

theorem entry_range (model : RationalCostModel) (S A : ℕ) (header : Header A)
    (hValid : Valid header) (hCap : header.region.stop < 2 ^ A)
    (entry : Entry A) (hEntry : entry ∈ (batch model S A header).entries) :
    header.region.start ≤ entry.location.value ∧ entry.location.value + A ≤ header.region.stop := by
  have hHeader := capacity header hValid hCap
  have hLocation := GeneralPaperReferenceSlotBatch.location_values model S A header.region.start header.fixed 1 0 0
    header.targets.length header.targets (by omega) (by decide) hHeader entry hEntry
  obtain ⟨i,target,_,hi,rfl⟩ := GeneralPaperReferenceSlotBatch.member_index model S A header.region.start header.fixed 1 0 0
    header.targets entry hEntry
  have hWithin := GeneralPaperReferenceSlotConstruction.within model S A header.region.start header.fixed 1
    header.targets.length i 0 target (by omega) (by decide)
  rw [hLocation]
  simp only [one_mul] at hWithin
  unfold Valid Region.stop at *
  constructor
  · exact hWithin.1
  · omega

theorem entry_key_in_region (model : RationalCostModel) (S A : ℕ) (header : Header A)
    (hA : 0 < A) (hValid : Valid header) (hCap : header.region.stop < 2 ^ A)
    (entry : Entry A) (hEntry : entry ∈ (batch model S A header).entries) :
    entry.location.value ∈ Set.Ico header.region.start header.region.stop := by
  have h := entry_range model S A header hValid hCap entry hEntry
  exact ⟨h.1,by omega⟩

theorem keys_nodup (model : RationalCostModel) (S A : ℕ) (header : Header A)
    (hA : 0 < A) (hValid : Valid header) (hCap : header.region.stop < 2 ^ A) :
    ((batch model S A header).entries.map (fun entry => entry.location.value)).Nodup :=
  GeneralPaperReferenceSlotBatch.keys_nodup model S A header.region.start header.fixed 1 0 0 header.targets.length header.targets
    hA (by omega) (by decide) (capacity header hValid hCap)

theorem disjoint_keys (model : RationalCostModel) (S A : ℕ) (first second : Header A)
    (hA : 0 < A) (hFirst : Valid first) (hSecond : Valid second)
    (hFirstCap : first.region.stop < 2 ^ A) (hSecondCap : second.region.stop < 2 ^ A)
    (hDisjoint : Disjoint (Set.Ico first.region.start first.region.stop) (Set.Ico second.region.start second.region.stop)) :
    List.Disjoint ((batch model S A first).entries.map (fun entry => entry.location.value))
      ((batch model S A second).entries.map (fun entry => entry.location.value)) := by
  apply List.disjoint_left.mpr
  intro key hKeyFirst hKeySecond
  obtain ⟨x,hx,hxKey⟩ := List.mem_map.mp hKeyFirst
  obtain ⟨y,hy,hyKey⟩ := List.mem_map.mp hKeySecond
  have h1 := entry_key_in_region model S A first hA hFirst hFirstCap x hx
  have h2 := entry_key_in_region model S A second hA hSecond hSecondCap y hy
  rw [hxKey] at h1
  rw [hyKey] at h2
  exact Set.disjoint_left.mp hDisjoint h1 h2

end Blotto.GeneralPaperReferenceRegionSlots
