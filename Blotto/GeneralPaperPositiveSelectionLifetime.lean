import Blotto.GeneralPaperPositiveScanLifetime

/-! Stored-index construction, positive scan, selected-list length traversal
and the returned list/count owner. The reserve sums the possible owned
buffers and pending frames across these phases; sharing and sequential
release can only reduce it. All sizes come from the actual stored input. -/
namespace Blotto.GeneralPaperPositiveSelectionLifetime
open scoped BigOperators
open GeneralPaperEncodedScalarStorage (natBits fields listFootprint)
open GeneralPaperPositiveScanLifetime (labelProfile labels_bound)
open GeneralPaperPreparedPositiveLabels (Selection)
set_option autoImplicit false
set_option maxHeartbeats 1800000

def traversalFrames (A r counter : ℕ) : ℕ :=
  ∑ j : Fin (r + 1), GeneralPaperIndexedArrayLifetime.frameFoot A r j.val counter

theorem traversal_bound (A r counter F : ℕ) (h : counter ≤ F) :
    traversalFrames A r counter ≤ (r + 1) * GeneralPaperIndexedArrayLifetime.frame A r F := by
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin (r + 1)) _ =>
    GeneralPaperIndexedArrayLifetime.frame_bound A r F j.val counter (by omega) h)
  simpa only [traversalFrames, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using hSum

def returned {n r : ℕ} {l : RationalSegmentLottery n r} (A : ℕ) (actual : Selection l × ℕ) : ℕ :=
  listFootprint A (fun j => natBits j.val) actual.1.data + fields A [actual.1.size, actual.2] + 64 * A

def reserve {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) : ℕ :=
  let ids := GeneralPaperEqualRouteConstruction.indices p.weights.data.size p.weights.size
  let actual := GeneralPaperPreparedPositiveLabels.run p model A
  let scanned := GeneralPaperPositiveLabelScan.scan model A p.weights ids
  2 * listFootprint A (fun j => natBits j.val) ids +
    traversalFrames A r (GeneralPaperEqualRouteConstruction.indicesWork A p.weights.data.size) +
    GeneralPaperPositiveScanLifetime.live p.weights model A ids +
    listFootprint A (fun j => natBits j.val) actual.1.data + traversalFrames A r actual.2 +
    fields A [r, actual.1.size, GeneralPaperEqualRouteConstruction.indicesWork A p.weights.data.size,
      scanned.2, actual.2] + 128 * A

def profile (model : RationalCostModel) (A r s : ℕ) : ℕ :=
  let F := GeneralPaperPreparedPositiveLabels.bound model A r s
  3 * labelProfile A r r + 2 * (r + 1) * GeneralPaperIndexedArrayLifetime.frame A r F +
    (r + 1) * (256 * (r * GeneralPaperPositiveLabelScan.stepBound model A r s + 32 * A + 32) +
      labelProfile A r r + 64 * A) + 5 * (natBits (r + F + 1) + A) + 160 * A

theorem bounded {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) (hs : 2 ≤ s) (h : ∀ j, RationalHeight (l.weight j) s) :
    reserve p model A ≤ profile model A r s := by
  let ids := GeneralPaperEqualRouteConstruction.indices p.weights.data.size p.weights.size
  let actual := GeneralPaperPreparedPositiveLabels.run p model A
  let scanned := GeneralPaperPositiveLabelScan.scan model A p.weights ids
  let F := GeneralPaperPreparedPositiveLabels.bound model A r s
  have hIds : ids.length = r := by
    dsimp only [ids]
    rw [GeneralPaperEqualRouteConstruction.indices_eq, List.length_finRange]
  have hSelected : actual.1.data.length ≤ r := by
    rw [← actual.1.size_correct]
    exact GeneralPaperPreparedPositiveLabels.size_le _
  have hIdsFoot := labels_bound A ids r hIds.le
  have hSelectedFoot := labels_bound A actual.1.data r hSelected
  have hWork : actual.2 ≤ F := GeneralPaperPreparedPositiveLabels.work p model A hs h
  have hTotal : actual.2 = scanned.2 + 2 * GeneralPaperEqualRouteConstruction.indicesWork A p.weights.data.size + 64 * A + 64 := rfl
  have hIndex : GeneralPaperEqualRouteConstruction.indicesWork A p.weights.data.size ≤ F := by omega
  have hIndexFrames := traversal_bound A r _ F hIndex
  have hCountFrames := traversal_bound A r actual.2 F hWork
  have hScan := GeneralPaperPositiveScanLifetime.height_bound p.weights model A ids hs
    (by intro j; rw [p.weight_correct]; exact h j) hIds.le
  have hSize := GeneralPaperPreparedPositiveLabels.size_le actual.1
  have hFields := GeneralPaperEncodedScalarStorage.fields_bound A (natBits (r + F + 1))
    [r, actual.1.size, GeneralPaperEqualRouteConstruction.indicesWork A p.weights.data.size, scanned.2, actual.2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 5 * (natBits (r + F + 1) + A) + 32 * A at hFields
  change 2 * listFootprint A (fun j => natBits j.val) ids +
    traversalFrames A r (GeneralPaperEqualRouteConstruction.indicesWork A p.weights.data.size) +
    GeneralPaperPositiveScanLifetime.live p.weights model A ids + listFootprint A (fun j => natBits j.val) actual.1.data +
    traversalFrames A r actual.2 + fields A [r, actual.1.size, GeneralPaperEqualRouteConstruction.indicesWork A p.weights.data.size, scanned.2, actual.2] + 128 * A ≤ _
  unfold profile
  change _ ≤ 3 * labelProfile A r r + 2 * (r + 1) * GeneralPaperIndexedArrayLifetime.frame A r F +
    (r + 1) * (256 * (r * GeneralPaperPositiveLabelScan.stepBound model A r s + 32 * A + 32) + labelProfile A r r + 64 * A) +
    5 * (natBits (r + F + 1) + A) + 160 * A
  nlinarith only [hIdsFoot, hSelectedFoot, hIndexFrames, hCountFrames, hScan, hFields]

theorem returned_bound {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) (hs : 2 ≤ s) (h : ∀ j, RationalHeight (l.weight j) s) :
    returned A (GeneralPaperPreparedPositiveLabels.run p model A) ≤
      labelProfile A r r + 2 * (natBits (r + GeneralPaperPreparedPositiveLabels.bound model A r s + 1) + A) + 96 * A := by
  let actual := GeneralPaperPreparedPositiveLabels.run p model A
  have hSize := GeneralPaperPreparedPositiveLabels.size_le actual.1
  have hData := labels_bound A actual.1.data r (by rw [← actual.1.size_correct]; exact hSize)
  have hWork : actual.2 ≤ GeneralPaperPreparedPositiveLabels.bound model A r s := GeneralPaperPreparedPositiveLabels.work p model A hs h
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A
    (r + GeneralPaperPreparedPositiveLabels.bound model A r s + 1) [actual.1.size, actual.2] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> omega)
  change fields A _ ≤ 2 * (natBits (r + GeneralPaperPreparedPositiveLabels.bound model A r s + 1) + A) + 32 * A at hFields
  change listFootprint A (fun j => natBits j.val) actual.1.data + fields A [actual.1.size, actual.2] + 64 * A ≤ _
  omega

end Blotto.GeneralPaperPositiveSelectionLifetime
