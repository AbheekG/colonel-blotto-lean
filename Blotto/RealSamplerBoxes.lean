import Blotto.RealNestedSpecSampler
import Blotto.NestedBoxes

/-! Every valid continuous input path stays inside the coordinate caps.
These bounds include zero-weight categorical paths and deterministic corners. -/

namespace Blotto
open scoped Classical

namespace SegmentLottery

theorem realSampleFlat_inBox {n k : ℕ} (l : SegmentLottery n k) (fallback : Fin k)
    (length : Allocation n) (hP : ∀ j, InBox length (l.P j)) (hQ : ∀ j, InBox length (l.Q j))
    (seed : Fin ((k - 1) + 1) → ℝ) (ht : 0 ≤ seed 0 ∧ seed 0 ≤ 1) :
    InBox length (l.realSampleFlat fallback seed) := by
  rw [l.realSampleFlat_refines]
  exact segment_inBox (hP _) (hQ _) ht

end SegmentLottery
namespace NestedInput

theorem realFirstPositive_inBox (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (hp : 0 < i.conditionalProbability s) (seed : Fin 9 → ℝ)
    (ht : 0 ≤ seed 0 ∧ seed 0 ≤ 1) : InBox ![i.a, i.d, i.c] (i.realFirstPositive htv s hs hp seed) := by
  rw [i.realFirstPositive_refines]
  let g := i.firstGeometry htv s hs hp
  have hDraw := g.segmentLottery.realSampleFlat_inBox 0 ![g.a, g.d, g.c]
    g.segmentLottery_box.1 g.segmentLottery_box.2 seed ht
  have he := i.firstGeometry_matches htv s hs hp
  have hCap : InBox ![i.a, i.d, i.c - s] (g.segmentLottery.realSampleFlat 0 seed) := by
    simpa only [g, he.1, he.2.1, he.2.2.1] using hDraw
  change InBox ![i.a, i.d, i.c] (shiftThird s (g.segmentLottery.realSampleFlat 0 seed))
  simpa only [sub_add_cancel] using shiftThird_inBox hs.1 hCap

theorem realFirstZero_inBox (i : NestedInput) (s : ℝ) (hs : 0 ≤ s ∧ s ≤ i.t)
    (seed : Fin 9 → ℝ) (ht : 0 ≤ seed 0 ∧ seed 0 ≤ 1) : InBox ![i.a, i.d, i.c] (i.realFirstZero s seed) := by
  rw [i.realFirstZero_refines]
  apply segment_inBox _ _ ht
  · intro j
    fin_cases j
    · exact ⟨le_rfl, le_of_lt i.a_pos⟩
    · exact ⟨le_of_lt i.d_pos, le_rfl⟩
    · exact ⟨hs.1, hs.2.trans i.t_lt.le⟩
  · intro j
    fin_cases j
    · exact ⟨le_of_lt i.a_pos, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt i.d_pos⟩
    · exact ⟨hs.1, hs.2.trans i.t_lt.le⟩

theorem realFirstConditional_inBox (i : NestedInput) (htv : i.t ≤ i.v) (s : ℝ)
    (hs : 0 ≤ s ∧ s ≤ i.t) (seed : Fin 9 → ℝ) (ht : 0 ≤ seed 0 ∧ seed 0 ≤ 1) :
    InBox ![i.a, i.d, i.c] (i.realFirstConditional htv s seed) := by
  rw [i.realFirstConditional_refines htv]
  change InBox ![i.a, i.d, i.c] (if hp : s ∈ i.positiveParameters then
    i.realFirstPositive htv s hp.1 hp.2 seed else i.realFirstZero s seed)
  split_ifs with hp
  · exact i.realFirstPositive_inBox htv s hp.1 hp.2 seed ht
  · exact i.realFirstZero_inBox s hs seed ht

theorem realFirstSample_inBox (i : NestedInput) (htv : i.t ≤ i.v) (seed : Fin 10 → ℝ)
    (hr : 0 ≤ seed 0 ∧ seed 0 ≤ 1) (ht : 0 ≤ seed 1 ∧ seed 1 ≤ 1) :
    InBox ![i.a, i.d, i.c] (i.realFirstSample htv seed) := by
  rw [i.realFirstSample_refines]
  exact i.realFirstConditional_inBox htv _ (i.location_bounds hr) (Fin.tail seed) ht

theorem realFamilyFirstSample_inBox (i : NestedInput) (x : ℝ) (hx : 0 < x) (hxv : x ≤ i.v)
    (seed : Fin 10 → ℝ) (hr : 0 ≤ seed 0 ∧ seed 0 ≤ 1) (ht : 0 ≤ seed 1 ∧ seed 1 ≤ 1) :
    InBox ![i.a, i.d, i.c] (i.realFamilyFirstSample x hx hxv seed) := by
  rw [i.realFamilyFirstSample_refines]
  exact (i.atLength x hx (by linarith [i.lengths.2.2.1])).realFirstSample_inBox hxv seed hr ht

theorem realSecondUniformSample_inBox (i : NestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t)
    (seed : Fin 10 → ℝ) (ht : 0 ≤ seed 1 ∧ seed 1 ≤ 1) :
    InBox ![i.a, i.d, i.c] (i.realSecondUniformSample htu hTt seed) := by
  rw [i.realSecondUniformSample_refines]
  let j := i.secondUniformInput htu hTt
  have hDraw : InBox ![i.a, i.d, i.t - i.mirrorLength] (j.segmentLottery.realSampleFlat 0 (Fin.tail seed)) :=
    j.segmentLottery.realSampleFlat_inBox 0 _ j.segmentLottery_box.1 j.segmentLottery_box.2 (Fin.tail seed) ht
  have hShift : InBox ![i.a, i.d, i.t]
      (shiftThird i.mirrorLength (j.segmentLottery.realSampleFlat 0 (Fin.tail seed))) := by
    simpa only [sub_add_cancel] using shiftThird_inBox (le_of_lt (i.mirrorLength_bounds htu).1) hDraw
  apply inBox_mono _ hShift
  intro k
  fin_cases k
  · exact le_rfl
  · exact le_rfl
  · exact i.t_lt.le

theorem realSecondSample_inBox (i : NestedInput) (htu : i.u ≤ i.t) (seed : Fin 11 → ℝ)
    (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) : InBox ![i.a, i.d, i.c] (i.realSecondSample htu seed) := by
  rw [i.realSecondSample_refines htu]
  change InBox ![i.a, i.d, i.c] (if hTt : i.mirrorLength < i.t then _ else _)
  split_ifs with hTt
  · exact realBinarySample_predicate _ _ _ seed (InBox ![i.a, i.d, i.c])
      (i.realFamilyFirstSample_inBox _ _ _ (Fin.tail seed) (h 1) (h 2))
      (i.realSecondUniformSample_inBox htu hTt (Fin.tail seed) (h 2))
  · exact i.realFamilyFirstSample_inBox _ _ _ (Fin.tail seed) (h 1) (h 2)

end NestedInput
namespace NestedResidual

theorem realSample_inBox (r : NestedResidual) (seed : Fin 10 → ℝ)
    (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) : InBox ![r.g.a, r.g.d, r.g.c] (r.realSample seed) := by
  rw [r.realSample_refines]
  exact r.segmentLottery.realSampleFlat_inBox 0 _ (fun _ => r.vertex_inBox _) (fun _ => r.vertex_inBox _)
    _ (RealUniformInputs.dropInputs_bounds 3 7 seed h 0)

end NestedResidual
namespace NestedInput

theorem realThirdSample_inBox (i : NestedInput) (hvt : i.v < i.t) (htu : i.t < i.u)
    (seed : Fin 11 → ℝ) (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) :
    InBox ![i.a, i.d, i.c] (i.realThirdSample hvt htu seed) := by
  have hResidual : InBox ![i.a, i.d, i.c] ((i.residualInput hvt htu).realSample (Fin.tail seed)) := by
    have he := i.geometry_matches
    simpa only [residualInput, he.1, he.2.1, he.2.2.1] using
      (i.residualInput hvt htu).realSample_inBox (Fin.tail seed) (fun j => h j.succ)
  unfold realThirdSample
  split_ifs with hv
  · exact realBinarySample_predicate _ _ _ seed (InBox ![i.a, i.d, i.c])
      (i.realFamilyFirstSample_inBox _ _ _ (Fin.tail seed) (h 1) (h 2)) hResidual
  · exact hResidual

theorem realSample_inBox (i : NestedInput) (seed : Fin 11 → ℝ)
    (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) : InBox ![i.a, i.d, i.c] (i.realSample seed) := by
  unfold realSample
  split_ifs with htv htu
  · exact i.realFirstSample_inBox htv (Fin.tail seed) (h 1) (h 2)
  · exact i.realSecondSample_inBox htu seed h
  · exact i.realThirdSample_inBox (lt_of_not_ge htv) (lt_of_not_ge htu) seed h

end NestedInput
namespace ThreeSpec

theorem realSample11_inBox (i : ThreeSpec) (seed : Fin 11 → ℝ)
    (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) : InBox ![i.a, i.d, i.c] (i.realSample11 seed) :=
  i.realSample_inBox _ (RealUniformInputs.dropInputs_bounds 9 2 seed h 0)

end ThreeSpec
namespace NestedSpec

theorem realSample_inBox (i : NestedSpec) (seed : Fin 11 → ℝ)
    (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) : InBox ![i.a, i.d, i.c] (i.realSample seed) := by
  unfold realSample
  split_ifs with hq0 hq1 had
  · exact (i.longInput hq0).realSample11_inBox seed h
  · have hb := (i.shortInput hq1).realSample11_inBox seed h
    apply inBox_mono _ hb
    intro j
    fin_cases j
    · exact le_rfl
    · exact le_rfl
    · exact i.t_lt.le
  · have hb := (i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0))
      (lt_of_le_of_ne i.q_le hq1)).realSample_inBox seed h
    simpa [interiorInput, min_eq_left had, max_eq_right had] using hb
  · have hda := (lt_of_not_ge had).le
    have hb := (i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0))
      (lt_of_le_of_ne i.q_le hq1)).realSample_inBox seed h
    intro j
    fin_cases j
    · simpa [swapFirst, interiorInput, max_eq_left hda] using hb 1
    · simpa [swapFirst, interiorInput, min_eq_right hda] using hb 0
    · simpa [swapFirst, interiorInput] using hb 2

end NestedSpec
end Blotto
