import Blotto.GeneralPaperCompactionArrayLifetime

/-! Every positive-compaction phase: index/scan/count selection, the three
active array prefixes, and final descriptor/price return. Full source rows
belong to the borrowed owner; compact endpoints own only row references.
The reserve includes completed array owners even during earlier phases. -/
namespace Blotto.GeneralPaperCompactionLifetime
open GeneralPaperEncodedScalarStorage (natBits fields)
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile)
open GeneralPaperCompactionArrayLifetime (selected weights left right resident residentProfile arrayTime)
open GeneralPaperPreparedSegmentCompaction (weightItem leftItem rightItem itemBound)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 2000000

inductive Phase (c : ℕ) where
  | selection
  | weight (i : Fin c)
  | left (i : Fin c)
  | right (i : Fin c)
  | returned

def controls {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) : ℕ :=
  fields A [r, (selected p model A).1.size, (selected p model A).2, (weights p model A).2,
    (left p model A).2, (right p model A).2,
    (weights p model A).2 + (left p model A).2 + (right p model A).2,
    (GeneralPaperPreparedSegmentCompaction.run p model A).2] + 128 * A

def controlProfile (model : RationalCostModel) (A r s : ℕ) : ℕ :=
  8 * (natBits (r + GeneralPaperPreparedSegmentCompaction.bound model A r s + 1) + A) + 160 * A

theorem controls_bound {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) (hs : 2 ≤ s) (h : ∀ j, RationalHeight (l.weight j) s) :
    controls p model A ≤ controlProfile model A r s := by
  have hTotal := (GeneralPaperCompactionArrayLifetime.source_components p model A).2.2.2
  have hWork := GeneralPaperPreparedSegmentCompaction.work p model A hs h
  have hSize := GeneralPaperPreparedPositiveLabels.size_le (selected p model A).1
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A
    (r + GeneralPaperPreparedSegmentCompaction.bound model A r s + 1)
    [r, (selected p model A).1.size, (selected p model A).2, (weights p model A).2,
      (left p model A).2, (right p model A).2,
      (weights p model A).2 + (left p model A).2 + (right p model A).2,
      (GeneralPaperPreparedSegmentCompaction.run p model A).2] (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 8 * (natBits (r + GeneralPaperPreparedSegmentCompaction.bound model A r s + 1) + A) + 32 * A at hFields
  unfold controls controlProfile
  omega

def arrayWindow {α : Type*} {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A borrowed : ℕ) (callback : Fin (count l) → α × ℕ) (encode : α → ℕ)
    (i : Fin (count l)) : ℕ :=
  GeneralPaperIndexedArrayLifetime.window id A callback encode i.val i.isLt.le (resident p model A borrowed)
    (GeneralPaperCompactionCallbackLifetime.footprint p (selected p model A).1 A i + controls p model A)

def window {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A borrowed : ℕ) : Phase (count l) → ℕ
  | .selection => borrowed + GeneralPaperPositiveSelectionLifetime.reserve p model A
  | .weight i => arrayWindow p model A borrowed (weightItem p (selected p model A).1 A) rationalWordWidth i
  | .left i => arrayWindow p model A borrowed (leftItem p (selected p model A).1 A) (fun _ => 0) i
  | .right i => arrayWindow p model A borrowed (rightItem p (selected p model A).1 A) (fun _ => 0) i
  | .returned => resident p model A borrowed + controls p model A

def profile (model : RationalCostModel) (A c r s borrowed : ℕ) : ℕ :=
  borrowed + GeneralPaperPositiveSelectionLifetime.profile model A r s + residentProfile model A c r s 0 +
    arrayProfile A c (1 + 2 * s) + (c + 1) * GeneralPaperIndexedArrayLifetime.frame A c (arrayTime A c r s) +
    GeneralPaperCompactionCallbackLifetime.profile A r s + controlProfile model A r s

theorem borrowed_mono (model : RationalCostModel) (A c r s B C : ℕ) (h : B ≤ C) :
    profile model A c r s B ≤ profile model A c r s C := by
  unfold profile
  omega

theorem array_phase {α : Type*} {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A borrowed : ℕ) (hs : 2 ≤ s) (h : ∀ j, RationalHeight (l.weight j) s)
    (callback : Fin (count l) → α × ℕ) (encode : α → ℕ)
    (hP : ∀ i, encode (callback i).1 ≤ 1 + 2 * s) (hW : ∀ i, (callback i).2 ≤ itemBound A r s)
    (i : Fin (count l)) :
    arrayWindow p model A borrowed callback encode i ≤ profile model A (count l) r s borrowed := by
  have hOwner := GeneralPaperCompactionArrayLifetime.resident_bound p model A borrowed hs h
  have hCallback := GeneralPaperCompactionCallbackLifetime.bounded p (selected p model A).1 A h i
  have hControl := controls_bound p model A hs h
  have hArrayTime := GeneralPaperPreparedSegmentCompaction.array_work (count l) rfl A _ callback hW
  rw [GeneralPaperSizedBitArray.eq_run] at hArrayTime
  change (PaperIndexedArrayConstruction.run id A callback).2 ≤ arrayTime A (count l) r s at hArrayTime
  have hFrames := GeneralPaperIndexedArrayLifetime.frame_mono A (count l) _ _ hArrayTime
  have hScaled := Nat.mul_le_mul_left (count l + 1) hFrames
  have hWindow := GeneralPaperIndexedArrayLifetime.window_bound id A callback encode (1 + 2 * s)
    (GeneralPaperCompactionCallbackLifetime.profile A r s + controlProfile model A r s) hP i.val i.isLt.le
    (resident p model A borrowed) _ (Nat.add_le_add hCallback hControl)
  change arrayWindow p model A borrowed callback encode i ≤ _ at hWindow
  unfold profile residentProfile at *
  omega

theorem all_phases {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A borrowed : ℕ) (hs : 2 ≤ s) (h : ∀ j, RationalHeight (l.weight j) s)
    (phase : Phase (count l)) :
    window p model A borrowed phase ≤ profile model A (count l) r s borrowed := by
  have hItems := GeneralPaperPreparedSegmentCompaction.item_work p (selected p model A).1 A h
  cases phase with
  | selection =>
    have hSelection := GeneralPaperPositiveSelectionLifetime.bounded p model A hs h
    change borrowed + GeneralPaperPositiveSelectionLifetime.reserve p model A ≤ _
    unfold profile
    omega
  | weight i =>
    exact array_phase p model A borrowed hs h _ _
      (GeneralPaperCompactionArrayLifetime.payload p _ A h) (fun j => (hItems j).1) i
  | left i => exact array_phase p model A borrowed hs h _ _ (fun _ => Nat.zero_le _) (fun j => (hItems j).2.1) i
  | right i => exact array_phase p model A borrowed hs h _ _ (fun _ => Nat.zero_le _) (fun j => (hItems j).2.2) i
  | returned =>
    have hOwner := GeneralPaperCompactionArrayLifetime.resident_bound p model A borrowed hs h
    have hControl := controls_bound p model A hs h
    change resident p model A borrowed + controls p model A ≤ _
    unfold profile residentProfile at *
    omega

end Blotto.GeneralPaperCompactionLifetime
