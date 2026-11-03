import Blotto.GeneralPaperPositiveLabelScan

/-! Retain the actual selected labels and their once-computed size. The
source index is erased; later compaction uses this stored list/count and
never reruns the probability formulas or the mathematical label filter. -/
namespace Blotto.GeneralPaperPreparedPositiveLabels
open GeneralPaperPositiveSegmentCompaction (labels count selected)
set_option autoImplicit false
set_option maxHeartbeats 1200000

structure Selection {n r : ℕ} (l : RationalSegmentLottery n r) where
  data : List (Fin r)
  correct : data = labels l
  size : ℕ
  size_correct : size = data.length

def run {n r : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) : Selection l × ℕ :=
  let ids := GeneralPaperEqualRouteConstruction.indices p.weights.data.size p.weights.size
  let actual := GeneralPaperPositiveLabelScan.scan model A p.weights ids
  let h : actual.1 = labels l := by
    rw [GeneralPaperPositiveLabelScan.data]
    dsimp only [ids]
    rw [GeneralPaperEqualRouteConstruction.indices_eq]
    simp only [labels, p.weight_correct]
  (⟨actual.1, h, actual.1.length, rfl⟩,
    actual.2 + 2 * GeneralPaperEqualRouteConstruction.indicesWork A p.weights.data.size + 64 * A + 64)

theorem size_eq {n r : ℕ} {l : RationalSegmentLottery n r} (s : Selection l) : s.size = count l := by
  rw [s.size_correct, s.correct]
  rfl

def Selection.read {n r : ℕ} {l : RationalSegmentLottery n r} (s : Selection l) (i : Fin (count l)) : Fin r :=
  s.data.get ⟨i.val, by rw [s.correct]; exact i.isLt⟩

theorem read_eq {n r : ℕ} {l : RationalSegmentLottery n r} (s : Selection l) (i : Fin (count l)) :
    s.read i = selected l i := by
  unfold Selection.read GeneralPaperPositiveSegmentCompaction.selected
  exact List.getElem_of_eq s.correct (by rw [s.correct]; exact i.isLt)

theorem size_le {n r : ℕ} {l : RationalSegmentLottery n r} (s : Selection l) : s.size ≤ r := by
  rw [s.size_correct, s.correct]
  exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := r))

def bound (model : RationalCostModel) (A r s : ℕ) : ℕ :=
  r * GeneralPaperPositiveLabelScan.stepBound model A r s +
    2 * GeneralPaperEqualRouteConstruction.indicesWork A r + 96 * (A + 1)

theorem work {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A : ℕ) (hs : 2 ≤ s) (h : ∀ j, RationalHeight (l.weight j) s) :
    (run p model A).2 ≤ bound model A r s := by
  have hp : ∀ j, RationalHeight (p.weights.read j) s := by intro j; rw [p.weight_correct]; exact h j
  have hScan := GeneralPaperPositiveLabelScan.work model A p.weights hs hp
    (GeneralPaperEqualRouteConstruction.indices p.weights.data.size p.weights.size)
  rw [GeneralPaperEqualRouteConstruction.indices_eq, List.length_finRange] at hScan
  unfold run bound
  dsimp only
  rw [GeneralPaperEqualRouteConstruction.indices_eq, p.weights.size]
  omega

end Blotto.GeneralPaperPreparedPositiveLabels
