import Blotto.PlayerSpecificSegmentAssemblyReference
import Blotto.DyadicSegmentLottery

/-! The finite midpoint laws commute with the actual descriptor assembly
operations. These are whole-allocation identities, including zero weights. -/
namespace Blotto.PlayerSpecificSegmentDyadicAssembly
open MeasureTheory
open PlayerSpecificSegmentAssemblyReference
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem pad {N k : ℕ} (l : SegmentLottery N k) (m K : ℕ) (fallback : Fin k) :
    (PlayerSpecificSegmentAssemblyReference.pad l m fallback).dyadicLaw K=l.dyadicLaw K := by
  apply ProbabilityMeasure.toMeasure_injective
  change (Measure.sum (fun slot => ENNReal.ofReal ((PlayerSpecificSegmentAssemblyReference.pad l m fallback).weight slot) •
    (dyadicSegmentLaw K ((PlayerSpecificSegmentAssemblyReference.pad l m fallback).P slot)
      ((PlayerSpecificSegmentAssemblyReference.pad l m fallback).Q slot) : Measure (Allocation N))))=_
  simp [PlayerSpecificSegmentAssemblyReference.pad,SegmentLottery.dyadicLaw,probabilityMixture,mixtureMeasure,
    Measure.sum_fintype,Fin.sum_univ_add]

theorem binary {N k m : ℕ} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (l : SegmentLottery N k) (r : SegmentLottery N m) (K : ℕ) :
    (PlayerSpecificSegmentAssemblyReference.binary p hp l r).dyadicLaw K=binaryLaw p hp (l.dyadicLaw K) (r.dyadicLaw K) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [binaryLaw_measure]
  change (Measure.sum (fun slot => ENNReal.ofReal ((PlayerSpecificSegmentAssemblyReference.binary p hp l r).weight slot) •
      (dyadicSegmentLaw K ((PlayerSpecificSegmentAssemblyReference.binary p hp l r).P slot)
        ((PlayerSpecificSegmentAssemblyReference.binary p hp l r).Q slot) : Measure (Allocation N))))=
    ENNReal.ofReal p • Measure.sum (fun slot => ENNReal.ofReal (l.weight slot) •
      (dyadicSegmentLaw K (l.P slot) (l.Q slot) : Measure (Allocation N)))+
    ENNReal.ofReal (1-p) • Measure.sum (fun slot => ENNReal.ofReal (r.weight slot) •
      (dyadicSegmentLaw K (r.P slot) (r.Q slot) : Measure (Allocation N)))
  simp only [PlayerSpecificSegmentAssemblyReference.binary,Measure.sum_fintype,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right]
  simp_rw [ENNReal.ofReal_mul hp.1,ENNReal.ofReal_mul (sub_nonneg.mpr hp.2),mul_smul]
  rw [Finset.smul_sum,Finset.smul_sum]

theorem mapped {N M k : ℕ} (l : SegmentLottery N k) (f : AffineAllocation N M) (K : ℕ) :
    ((l.mapped f).dyadicLaw K : Measure (Allocation M))=Measure.map f.value (l.dyadicLaw K : Measure (Allocation N)) := by
  change mixtureMeasure l.weight (fun slot => dyadicSegmentLaw K (f.value (l.P slot)) (f.value (l.Q slot)))=
    Measure.map f.value (mixtureMeasure l.weight (fun slot => dyadicSegmentLaw K (l.P slot) (l.Q slot)))
  rw [mixtureMeasure_map _ _ _ f.measurable]
  unfold mixtureMeasure
  congr 1
  funext slot
  have he : Measure.map f.value (dyadicSegmentLaw K (l.P slot) (l.Q slot) : Measure (Allocation N))=
      (dyadicSegmentLaw K (f.value (l.P slot)) (f.value (l.Q slot)) : Measure (Allocation M)) := by
    change Measure.map f.value (Measure.map (dyadicSegmentPoint K (l.P slot) (l.Q slot))
      (fairBitLaw K : Measure (Fin K → Bool)))=_
    rw [Measure.map_map f.measurable (measurable_of_countable _)]
    congr 1
    funext bits
    exact f.onSegment _ _ _
  rw [he]

end Blotto.PlayerSpecificSegmentDyadicAssembly
