import Blotto.PlayerSpecificAlgebraicNestedFirstDrawSizes
import Blotto.BinaryMixture

/-! Real finite-lottery references for actual algebraic padding and
binary table assembly. They preserve full laws without listing allocations. -/
namespace Blotto.PlayerSpecificSegmentAssemblyReference
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def pad {N k : ℕ} (l : SegmentLottery N k) (m : ℕ) (fallback : Fin k) : SegmentLottery N (k+m) where
  weight := Fin.addCases l.weight (fun _ => 0)
  P := Fin.addCases l.P (fun _ => l.P fallback)
  Q := Fin.addCases l.Q (fun _ => l.Q fallback)
  nonnegative := by
    intro slot
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [Fin.addCases_left] using l.nonnegative j
    · intro j; simp only [Fin.addCases_right]; exact le_rfl
  mass := by rw [Fin.sum_univ_add]; simp [l.mass]

noncomputable def binary {N k m : ℕ} (p : ℝ) (hp : 0≤p ∧ p≤1)
    (l : SegmentLottery N k) (r : SegmentLottery N m) : SegmentLottery N (k+m) where
  weight := Fin.addCases (fun j => p*l.weight j) (fun j => (1-p)*r.weight j)
  P := Fin.addCases l.P r.P
  Q := Fin.addCases l.Q r.Q
  nonnegative := by
    intro slot
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa only [Fin.addCases_left] using mul_nonneg hp.1 (l.nonnegative j)
    · intro j; simpa only [Fin.addCases_right] using mul_nonneg (sub_nonneg.mpr hp.2) (r.nonnegative j)
  mass := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left,Fin.addCases_right,←Finset.mul_sum,l.mass,r.mass,mul_one]
    ring

theorem pad_law {N k : ℕ} (l : SegmentLottery N k) (m : ℕ) (fallback : Fin k) : (pad l m fallback).law=l.law := by
  apply ProbabilityMeasure.toMeasure_injective
  change (Measure.sum (fun slot => ENNReal.ofReal ((pad l m fallback).weight slot) •
    (segmentLaw ((pad l m fallback).P slot) ((pad l m fallback).Q slot) : Measure (Allocation N))))=_
  simp [pad,SegmentLottery.law,probabilityMixture,mixtureMeasure,Measure.sum_fintype,Fin.sum_univ_add]

theorem binary_law {N k m : ℕ} (p : ℝ) (hp : 0≤p ∧ p≤1) (l : SegmentLottery N k) (r : SegmentLottery N m) :
    (binary p hp l r).law=binaryLaw p hp l.law r.law := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [binaryLaw_measure]
  change (Measure.sum (fun slot => ENNReal.ofReal ((binary p hp l r).weight slot) •
      (segmentLaw ((binary p hp l r).P slot) ((binary p hp l r).Q slot) : Measure (Allocation N))))=
    ENNReal.ofReal p • Measure.sum (fun slot => ENNReal.ofReal (l.weight slot) •
      (segmentLaw (l.P slot) (l.Q slot) : Measure (Allocation N)))+
    ENNReal.ofReal (1-p) • Measure.sum (fun slot => ENNReal.ofReal (r.weight slot) •
      (segmentLaw (r.P slot) (r.Q slot) : Measure (Allocation N)))
  simp only [binary,Measure.sum_fintype,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right]
  simp_rw [ENNReal.ofReal_mul hp.1,ENNReal.ofReal_mul (sub_nonneg.mpr hp.2),mul_smul]
  rw [Finset.smul_sum,Finset.smul_sum]

end Blotto.PlayerSpecificSegmentAssemblyReference
