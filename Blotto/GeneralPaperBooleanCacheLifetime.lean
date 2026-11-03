import Blotto.GeneralPaperBooleanRowsLifetime

/-! Full Boolean-cache phase reserve. Final payload is conservatively
reserved alongside active encoding/list/ruler buffers and all work records.
This is observation of the existing constructor, not a cache rebuild. -/
namespace Blotto.GeneralPaperBooleanCacheLifetime
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperPositiveSegmentCompaction (count)
open GeneralPaperEncodedScalarStorage (natBits fields listFootprint)
set_option autoImplicit false
set_option maxHeartbeats 2000000


def labelsLive {c : ℕ} (A : ℕ) (counts : FixedArrayTable c ℕ) : ℕ :=
  let ids := GeneralPaperEqualRouteConstruction.indices counts.data.size counts.size
  let F := GeneralPaperEqualRouteConstruction.indicesWork A counts.data.size
  2 * listFootprint A (fun i => natBits i.val) ids + GeneralPaperPositiveSelectionLifetime.traversalFrames A c F +
    fields A [c, F] + 128 * A

def labelsProfile (A c : ℕ) : ℕ :=
  let F := GeneralPaperEqualRouteConstruction.indicesWork A c
  2 * GeneralPaperPositiveScanLifetime.labelProfile A c c + (c + 1) * GeneralPaperIndexedArrayLifetime.frame A c F +
    2 * (natBits (c + F + 1) + A) + 160 * A

theorem labels_bound {c : ℕ} (A : ℕ) (counts : FixedArrayTable c ℕ) : labelsLive A counts ≤ labelsProfile A c := by
  let ids := GeneralPaperEqualRouteConstruction.indices counts.data.size counts.size
  let F := GeneralPaperEqualRouteConstruction.indicesWork A c
  have hIds : ids.length = c := by dsimp only [ids]; rw [GeneralPaperEqualRouteConstruction.indices_eq, List.length_finRange]
  have hList := GeneralPaperPositiveScanLifetime.labels_bound A ids c hIds.le
  have hFrames := GeneralPaperPositiveSelectionLifetime.traversal_bound A c F F le_rfl
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (c + F + 1) [c, F] (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> omega)
  change fields A _ ≤ 2 * (natBits (c + F + 1) + A) + 32 * A at hFields
  change 2 * listFootprint A (fun i => natBits i.val) ids + GeneralPaperPositiveSelectionLifetime.traversalFrames A c (GeneralPaperEqualRouteConstruction.indicesWork A counts.data.size) +
    fields A [c, GeneralPaperEqualRouteConstruction.indicesWork A counts.data.size] + 128 * A ≤ _
  rw [counts.size]
  change 2 * listFootprint A (fun i => natBits i.val) ids + GeneralPaperPositiveSelectionLifetime.traversalFrames A c F + fields A [c, F] + 128 * A ≤ _
  change _ ≤ 2 * GeneralPaperPositiveScanLifetime.labelProfile A c c + (c + 1) * GeneralPaperIndexedArrayLifetime.frame A c F +
    2 * (natBits (c + F + 1) + A) + 160 * A
  omega

def rulerLive (A width copied : ℕ) : ℕ :=
  listFootprint A (fun _ : Unit => 0) (List.replicate copied ()) +
    (width + 1) * GeneralPaperIndexedArrayLifetime.frameFoot A width copied 0 + 64 * A

def rulerProfile (A width : ℕ) : ℕ :=
  width * (2 * A) + 32 * A + (width + 1) * GeneralPaperIndexedArrayLifetime.frame A width 0 + 64 * A

theorem ruler_bound (A width copied : ℕ) (h : copied ≤ width) : rulerLive A width copied ≤ rulerProfile A width := by
  have hList := GeneralPaperEncodedScalarStorage.list_bound A 0 (fun _ : Unit => 0) (List.replicate copied ()) (by intro _ _; exact le_rfl)
  simp only [List.length_replicate, zero_add] at hList
  have hFrames := Nat.mul_le_mul_left (width + 1) (GeneralPaperIndexedArrayLifetime.frame_bound A width 0 copied 0 h le_rfl)
  have hScale := Nat.mul_le_mul_right (2 * A) h
  unfold rulerLive rulerProfile
  omega

def controls {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Prepared G l) (model : RationalCostModel) (A : ℕ) : ℕ :=
  let den := GeneralPaperStoredWordEncoding.word model A (p.rangeBits + 1) p.D
  let ids := GeneralPaperEqualRouteConstruction.indices p.counts.data.size p.counts.size
  let rows := GeneralPaperStoredBooleanCache.rows p.counts model A (p.rangeBits + 1) ids
  let indices := GeneralPaperEqualRouteConstruction.indicesWork A p.counts.data.size
  let ruler := 64 * (p.rangeBits + 1) * (A + binaryWordWidth (p.rangeBits + 1) + 1)
  fields A [count l, p.rangeBits, den.2, rows.2, indices, ruler, (GeneralPaperStoredBooleanCache.run p model A).2] + 128 * A

def controlProfile (model : RationalCostModel) (A c width L : ℕ) : ℕ :=
  7 * (natBits (c + width + GeneralPaperStoredBooleanCache.bound model A c width L + 1) + A) + 160 * A

theorem controls_bound {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Prepared G l) (model : RationalCostModel) (A L : ℕ) (hD : binaryWordWidth p.D ≤ L) :
    controls p model A ≤ controlProfile model A (count l) p.rangeBits L := by
  let den := GeneralPaperStoredWordEncoding.word model A (p.rangeBits + 1) p.D
  let ids := GeneralPaperEqualRouteConstruction.indices p.counts.data.size p.counts.size
  let rows := GeneralPaperStoredBooleanCache.rows p.counts model A (p.rangeBits + 1) ids
  let indices := GeneralPaperEqualRouteConstruction.indicesWork A p.counts.data.size
  let ruler := 64 * (p.rangeBits + 1) * (A + binaryWordWidth (p.rangeBits + 1) + 1)
  let F := (GeneralPaperStoredBooleanCache.run p model A).2
  have hTotal : F = den.2 + rows.2 + indices + ruler + 128 * A + 128 := rfl
  have hWork : F ≤ GeneralPaperStoredBooleanCache.bound model A (count l) p.rangeBits L := GeneralPaperStoredBooleanCache.work p model A L hD
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A
    (count l + p.rangeBits + GeneralPaperStoredBooleanCache.bound model A (count l) p.rangeBits L + 1)
    [count l, p.rangeBits, den.2, rows.2, indices, ruler, F] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 7 * (natBits (count l + p.rangeBits + GeneralPaperStoredBooleanCache.bound model A (count l) p.rangeBits L + 1) + A) + 32 * A at hFields
  change fields A [count l, p.rangeBits, den.2, rows.2, indices, ruler, F] + 128 * A ≤ _
  unfold controlProfile
  omega

inductive Phase (width : ℕ) where
  | denominator
  | labels
  | rows
  | ruler (copied : ℕ) (h : copied ≤ width)
  | returned

def window {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Prepared G l) (model : RationalCostModel) (A borrowed : ℕ) (phase : Phase p.rangeBits) : ℕ :=
  borrowed + GeneralPaperEqualRetainedStorage.cacheFoot A (GeneralPaperStoredBooleanCache.run p model A).1 + controls p model A +
    match phase with
    | .denominator => GeneralPaperWordEncodingLifetime.window model A (p.rangeBits + 1) p.D
    | .labels => labelsLive A p.counts
    | .rows => GeneralPaperBooleanRowsLifetime.live p.counts model A (p.rangeBits + 1)
        (GeneralPaperEqualRouteConstruction.indices p.counts.data.size p.counts.size)
    | .ruler copied _ => rulerLive A p.rangeBits copied
    | .returned => 0

def profile (model : RationalCostModel) (A c width L borrowed : ℕ) : ℕ :=
  borrowed + GeneralPaperEqualRetainedStorage.cacheProfile A c width + controlProfile model A c width L +
    GeneralPaperWordEncodingLifetime.windowProfile model A (width + 1) L + labelsProfile A c +
    GeneralPaperBooleanRowsLifetime.profile model A c (width + 1) L + rulerProfile A width

theorem borrowed_mono (model : RationalCostModel) (A c width L B C : ℕ) (h : B ≤ C) :
    profile model A c width L B ≤ profile model A c width L C := by unfold profile; omega

theorem all_phases {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Prepared G l) (model : RationalCostModel) (A L borrowed : ℕ) (hD : binaryWordWidth p.D ≤ L)
    (phase : Phase p.rangeBits) : window p model A borrowed phase ≤ profile model A (count l) p.rangeBits L borrowed := by
  have hCache := GeneralPaperEqualRetainedStorage.cache_bound A (GeneralPaperStoredBooleanCache.run p model A).1
  have hControls := controls_bound p model A L hD
  have hCounts : ∀ i, binaryWordWidth (p.counts.read i) ≤ L := fun i =>
    (binaryWordWidth_mono (GeneralPaperEqualPreparedCache.counts_bounded p i)).trans hD
  cases phase with
  | denominator =>
    have hWord := GeneralPaperWordEncodingLifetime.word_bound model A (p.rangeBits + 1) p.D L hD
    simp only [window]
    unfold profile
    omega
  | labels =>
    have hLabels := labels_bound A p.counts
    simp only [window]
    unfold profile
    omega
  | rows =>
    have hRows := GeneralPaperBooleanRowsLifetime.all_rows p.counts model A (p.rangeBits + 1) L hCounts
    simp only [window]
    unfold profile
    omega
  | ruler copied h =>
    have hRuler := ruler_bound A p.rangeBits copied h
    simp only [window]
    unfold profile
    omega
  | returned =>
    simp only [window]
    unfold profile
    omega

end Blotto.GeneralPaperBooleanCacheLifetime
