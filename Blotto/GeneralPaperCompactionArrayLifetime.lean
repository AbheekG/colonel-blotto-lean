import Blotto.GeneralPaperCompactionCallbackLifetime

/-! Compact probability and endpoint-reference arrays. The owner counts one
reference per endpoint row; its rational payload is borrowed from the full
segment descriptor. Completed owners are conservatively reserved during
all three array passes, together with the selected list/count. -/
namespace Blotto.GeneralPaperCompactionArrayLifetime
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile array_bound)
open GeneralPaperEncodedScalarStorage (natBits)
open GeneralPaperPreparedPositiveLabels (Selection)
open GeneralPaperPreparedSegmentCompaction (weightItem leftItem rightItem itemBound)
open GeneralPaperPositiveSegmentCompaction (count)
open GeneralPaperSegmentCompilerStorage (owner)
set_option autoImplicit false
set_option maxHeartbeats 1800000

def arrayTime (A c r s : ℕ) : ℕ := c * itemBound A r s + PaperIndexedArrayConstruction.overhead id A c c

def ownerProfile (A c r s : ℕ) : ℕ := arrayProfile A c (1 + 2 * s) + natBits (arrayTime A c r s) + 64 * A

theorem completed {α : Type*} {c : ℕ} (size : ℕ) (hSize : size = c) (A r s : ℕ)
    (callback : Fin c → α × ℕ) (encode : α → ℕ)
    (hP : ∀ i, encode (callback i).1 ≤ 1 + 2 * s) (hWork : ∀ i, (callback i).2 ≤ itemBound A r s) :
    owner A (arrayFootprint A encode) (GeneralPaperSizedBitArray.run size hSize A callback) ≤ ownerProfile A c r s := by
  apply GeneralPaperSegmentCompilerStorage.owner_bound A _ _ _ _
  · rw [GeneralPaperSizedBitArray.eq_run, PaperIndexedArrayConstruction.run_data]
    exact array_bound A _ encode _ (by intro i; rw [FixedArrayTable.read_ofFn]; exact hP i)
  · exact GeneralPaperPreparedSegmentCompaction.array_work size hSize A _ callback hWork

def selected {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l) (model : RationalCostModel) (A : ℕ) :=
  GeneralPaperPreparedPositiveLabels.run p model A

def weights {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l) (model : RationalCostModel) (A : ℕ) :=
  GeneralPaperSizedBitArray.run (selected p model A).1.size (GeneralPaperPreparedPositiveLabels.size_eq _) A
    (weightItem p (selected p model A).1 A)

def left {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l) (model : RationalCostModel) (A : ℕ) :=
  GeneralPaperSizedBitArray.run (selected p model A).1.size (GeneralPaperPreparedPositiveLabels.size_eq _) A
    (leftItem p (selected p model A).1 A)

def right {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l) (model : RationalCostModel) (A : ℕ) :=
  GeneralPaperSizedBitArray.run (selected p model A).1.size (GeneralPaperPreparedPositiveLabels.size_eq _) A
    (rightItem p (selected p model A).1 A)

def selectionProfile (model : RationalCostModel) (A r s : ℕ) : ℕ :=
  GeneralPaperPositiveScanLifetime.labelProfile A r r +
    2 * (natBits (r + GeneralPaperPreparedPositiveLabels.bound model A r s + 1) + A) + 96 * A

def resident {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A borrowed : ℕ) : ℕ :=
  borrowed + GeneralPaperPositiveSelectionLifetime.returned A (selected p model A) +
    owner A (arrayFootprint A rationalWordWidth) (weights p model A) +
    owner A (arrayFootprint A (fun _ => 0)) (left p model A) +
    owner A (arrayFootprint A (fun _ => 0)) (right p model A)

def residentProfile (model : RationalCostModel) (A c r s borrowed : ℕ) : ℕ :=
  borrowed + selectionProfile model A r s + 3 * ownerProfile A c r s

theorem payload {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l) (chosen : Selection l)
    (A : ℕ) (h : ∀ j, RationalHeight (l.weight j) s) (i : Fin (count l)) :
    rationalWordWidth (weightItem p chosen A i).1 ≤ 1 + 2 * s := by
  change rationalWordWidth (p.weights.read (chosen.read i)) ≤ _
  rw [p.weight_correct]
  exact rationalWordWidth_of_height (h _)

theorem resident_bound {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A borrowed : ℕ) (hs : 2 ≤ s) (h : ∀ j, RationalHeight (l.weight j) s) :
    resident p model A borrowed ≤ residentProfile model A (count l) r s borrowed := by
  have hItems := GeneralPaperPreparedSegmentCompaction.item_work p (selected p model A).1 A h
  have hW := completed (selected p model A).1.size (GeneralPaperPreparedPositiveLabels.size_eq _) A r s
    (weightItem p (selected p model A).1 A) rationalWordWidth (payload p _ A h) (fun i => (hItems i).1)
  have hL := completed (selected p model A).1.size (GeneralPaperPreparedPositiveLabels.size_eq _) A r s
    (leftItem p (selected p model A).1 A) (fun _ => 0) (fun _ => Nat.zero_le _) (fun i => (hItems i).2.1)
  have hR := completed (selected p model A).1.size (GeneralPaperPreparedPositiveLabels.size_eq _) A r s
    (rightItem p (selected p model A).1 A) (fun _ => 0) (fun _ => Nat.zero_le _) (fun i => (hItems i).2.2)
  change owner A (arrayFootprint A rationalWordWidth) (weights p model A) ≤ _ at hW
  change owner A (arrayFootprint A (fun _ => 0)) (left p model A) ≤ _ at hL
  change owner A (arrayFootprint A (fun _ => 0)) (right p model A) ≤ _ at hR
  have hSelection : GeneralPaperPositiveSelectionLifetime.returned A (selected p model A) ≤ selectionProfile model A r s :=
    GeneralPaperPositiveSelectionLifetime.returned_bound p model A hs h
  unfold resident residentProfile
  omega

theorem source_components {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) :
    let actual := GeneralPaperPreparedSegmentCompaction.run p model A
    actual.1.weights = (weights p model A).1 ∧ actual.1.left = (left p model A).1 ∧
      actual.1.right = (right p model A).1 ∧
      actual.2 = (selected p model A).2 + (weights p model A).2 + (left p model A).2 + (right p model A).2 + 128 * A + 128 := by
  simp only [GeneralPaperPreparedSegmentCompaction.run, GeneralPaperPreparedSegmentCompaction.make,
    selected, weights, left, right]
  exact ⟨True.intro, True.intro, True.intro, by omega⟩

end Blotto.GeneralPaperCompactionArrayLifetime
