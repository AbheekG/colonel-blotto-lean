import Blotto.GeneralPaperEqualUncappedSamplingContract
import Blotto.PreparedSegmentDescriptorHeight

/-! Native removal of zero-weight segment slots. The prepared list contains
only positive entries, in source order; no allocation support is enumerated.
Both continuous and finite-midpoint whole laws are preserved exactly. -/
namespace Blotto.GeneralPaperPositiveSegmentCompaction
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 600000

def labels {n k : ℕ} (l : RationalSegmentLottery n k) : List (Fin k) :=
  (List.finRange k).filter (fun j => decide (0 < l.weight j))

def count {n k : ℕ} (l : RationalSegmentLottery n k) : ℕ := (labels l).length

def selected {n k : ℕ} (l : RationalSegmentLottery n k) (i : Fin (count l)) : Fin k :=
  (labels l).get i

theorem labels_mem {n k : ℕ} (l : RationalSegmentLottery n k) (j : Fin k) :
    j ∈ labels l ↔ 0 < l.weight j := by simp [labels]

theorem labels_nodup {n k : ℕ} (l : RationalSegmentLottery n k) : (labels l).Nodup :=
  (List.nodup_finRange k).filter _

theorem selected_positive {n k : ℕ} (l : RationalSegmentLottery n k) (i : Fin (count l)) :
    0 < l.weight (selected l i) := (labels_mem l _).mp (List.get_mem _ i)

theorem sum_get_labels {n k : ℕ} (l : RationalSegmentLottery n k)
    {α : Type*} [AddCommMonoid α] (f : Fin k → α) :
    (∑ i : Fin (count l), f (selected l i)) = ((labels l).map f).sum := by
  rw [← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map (labels l) f)

theorem sum_selected {n k : ℕ} (l : RationalSegmentLottery n k)
    {α : Type*} [AddCommMonoid α] (f : Fin k → α) (hz : ∀ j, l.weight j = 0 → f j = 0) :
    (∑ i : Fin (count l), f (selected l i)) = ∑ j, f j := by
  classical
  rw [sum_get_labels, ← List.sum_toFinset f (labels_nodup l)]
  have hSet : (labels l).toFinset = Finset.univ.filter (fun j => 0 < l.weight j) := by
    ext j
    simp only [List.mem_toFinset, labels_mem, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hSet, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : 0 < l.weight j
  · simp only [h, ite_true]
  · have h0 : l.weight j = 0 := le_antisymm (le_of_not_gt h) (l.nonnegative j)
    simp only [h, ite_false, hz j h0]

def compact {n k : ℕ} (l : RationalSegmentLottery n k) : RationalSegmentLottery n (count l) where
  weight := fun i => l.weight (selected l i)
  P := fun i => l.P (selected l i)
  Q := fun i => l.Q (selected l i)
  nonnegative := fun i => (selected_positive l i).le
  mass := (sum_selected l l.weight (fun _ h => h)).trans l.mass

theorem count_positive {n k : ℕ} (l : RationalSegmentLottery n k) : 0 < count l := by
  have hs : ((labels l).map l.weight).sum = 1 := by
    have h := (sum_selected l l.weight (fun _ h => h)).trans l.mass
    rw [sum_get_labels] at h
    exact h
  by_contra h
  have he : labels l = [] := List.length_eq_zero_iff.mp (by unfold count at h; omega)
  simp [he] at hs

theorem count_card {n k : ℕ} (l : RationalSegmentLottery n k) :
    count l = l.real.positiveSlots.card := by
  classical
  have hSet : (labels l).toFinset = l.real.positiveSlots := by
    ext j
    rw [List.mem_toFinset, labels_mem]
    unfold SegmentLottery.positiveSlots
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (0 < l.weight j) ↔ (0 : ℝ) < (l.weight j : ℝ)
    exact_mod_cast Iff.rfl
  rw [count, ← List.toFinset_card_of_nodup (labels_nodup l), hSet]

theorem compact_law {n k : ℕ} (l : RationalSegmentLottery n k) :
    (compact l).real.law = l.real.law := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [SegmentLottery.law_measure, SegmentLottery.law_measure]
  simp only [Measure.sum_fintype]
  change (∑ i : Fin (count l), ENNReal.ofReal (l.weight (selected l i) : ℝ) •
    (segmentLaw (fun j => (l.P (selected l i) j : ℝ))
      (fun j => (l.Q (selected l i) j : ℝ)) : Measure (Allocation n))) = _
  exact sum_selected l (fun i => ENNReal.ofReal (l.weight i : ℝ) •
    (segmentLaw (fun j => (l.P i j : ℝ)) (fun j => (l.Q i j : ℝ)) : Measure (Allocation n)))
    (fun j h => by simp only [h, Rat.cast_zero, ENNReal.ofReal_zero, zero_smul])

theorem compact_dyadic_law {n k : ℕ} (l : RationalSegmentLottery n k) (K : ℕ) :
    (compact l).real.dyadicLaw K = l.real.dyadicLaw K := by
  apply ProbabilityMeasure.toMeasure_injective
  change (Measure.sum (fun i : Fin (count l) => ENNReal.ofReal (l.weight (selected l i) : ℝ) •
    (dyadicSegmentLaw K (fun j => (l.P (selected l i) j : ℝ))
      (fun j => (l.Q (selected l i) j : ℝ)) : Measure (Allocation n)))) =
    Measure.sum (fun i : Fin k => ENNReal.ofReal (l.weight i : ℝ) •
      (dyadicSegmentLaw K (fun j => (l.P i j : ℝ)) (fun j => (l.Q i j : ℝ)) : Measure (Allocation n)))
  simp only [Measure.sum_fintype]
  exact sum_selected l (fun i => ENNReal.ofReal (l.weight i : ℝ) •
    (dyadicSegmentLaw K (fun j => (l.P i j : ℝ)) (fun j => (l.Q i j : ℝ)) : Measure (Allocation n)))
    (fun j h => by simp only [h, Rat.cast_zero, ENNReal.ofReal_zero, zero_smul])

theorem compact_height {n k s : ℕ} (l : RationalSegmentLottery n k) (h : l.HeightAt s) :
    (compact l).HeightAt s := ⟨fun i => h.1 (selected l i), fun i j => h.2 (selected l i) j⟩

theorem compact_endpoints {n k : ℕ} (l : RationalSegmentLottery n k) (B : ℝ)
    (h : ∀ i, FullBudget B (l.real.P i) ∧ FullBudget B (l.real.Q i)) :
    ∀ i, FullBudget B ((compact l).real.P i) ∧ FullBudget B ((compact l).real.Q i) := fun i => h (selected l i)

end Blotto.GeneralPaperPositiveSegmentCompaction
