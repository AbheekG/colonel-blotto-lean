import Blotto.RationalLotteryBoxes
import Blotto.ReflectAppend

/-! Native affine allocation maps stored as rational matrices and offsets.
Their real interpretation is affine on every segment; applying them to a
descriptor preserves weights and the exact push-forward law. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

structure RationalAffineAllocation (n m : ℕ) where
  coefficient : Fin m → Fin n → ℚ
  offset : Fin m → ℚ

namespace RationalAffineAllocation

def value {n m : ℕ} (f : RationalAffineAllocation n m) (x : Fin n → ℚ) : Fin m → ℚ :=
  fun i => (∑ j, f.coefficient i j * x j) + f.offset i

noncomputable def real {n m : ℕ} (f : RationalAffineAllocation n m) : AffineAllocation n m where
  value := fun x i => (∑ j, (f.coefficient i j : ℝ) * x j) + (f.offset i : ℝ)
  measurable := by
    apply Measurable.of_eval
    intro i
    exact (Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_pi_apply j))).add measurable_const
  onSegment := by
    intro P Q t
    funext i
    simp only [segmentPoint, Finset.sum_add_distrib, mul_add]
    have hP : (∑ j, (f.coefficient i j : ℝ) * ((1 - t) * P j)) =
        (1 - t) * ∑ j, (f.coefficient i j : ℝ) * P j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hQ : (∑ j, (f.coefficient i j : ℝ) * (t * Q j)) = t * ∑ j, (f.coefficient i j : ℝ) * Q j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hP, hQ]
    ring

theorem value_real {n m : ℕ} (f : RationalAffineAllocation n m) (x : Fin n → ℚ) :
    (fun i => (f.value x i : ℝ)) = f.real.value (fun j => (x j : ℝ)) := by
  funext i
  simp [value, real]

def splitFirstTwo (a d : ℚ) : RationalAffineAllocation 3 4 where
  coefficient := ![![a / (a + d), 0, 0], ![d / (a + d), 0, 0], ![0, 1, 0], ![0, 0, 1]]
  offset := fun _ => 0

theorem splitFirstTwo_real (a d : ℚ) (x : Allocation 3) :
    (splitFirstTwo a d).real.value x = Blotto.splitFirstTwo (a : ℝ) (d : ℝ) x := by
  funext i
  fin_cases i <;> simp [splitFirstTwo, real, Blotto.splitFirstTwo, Fin.sum_univ_succ]

def reflectAppend (length : Fin 3 → ℚ) : RationalAffineAllocation 3 4 where
  coefficient := ![![-1, 0, 0], ![0, -1, 0], ![0, 0, -1], ![0, 0, 0]]
  offset := ![length 0, length 1, length 2, 0]

theorem reflectAppend_real (length : Fin 3 → ℚ) (x : Allocation 3) :
    (reflectAppend length).real.value x = Blotto.reflectAppend (fun j => (length j : ℝ)) x := by
  funext i
  fin_cases i <;> simp [reflectAppend, real, Blotto.reflectAppend, Fin.sum_univ_succ]
  all_goals ring

def permutation {n : ℕ} (π : Equiv.Perm (Fin n)) : RationalAffineAllocation n n where
  coefficient := fun i j => if j = π i then 1 else 0
  offset := fun _ => 0

theorem permutation_real {n : ℕ} (π : Equiv.Perm (Fin n)) (x : Allocation n) :
    (permutation π).real.value x = permuteAllocation π x := by
  funext i
  simp [permutation, real, permuteAllocation]
  have h : ∀ j, ((if j = π i then 1 else 0 : ℚ) : ℝ) * x j = if j = π i then x j else 0 := by
    intro j
    by_cases hj : j = π i <;> simp [hj]
  simp_rw [h]
  simp

end RationalAffineAllocation

namespace RationalSegmentLottery

def mapped {n m k : ℕ} (l : RationalSegmentLottery n k) (f : RationalAffineAllocation n m) : RationalSegmentLottery m k :=
  ⟨l.weight, (fun slot => f.value (l.P slot)), (fun slot => f.value (l.Q slot)), l.nonnegative, l.mass⟩

theorem mapped_real {n m k : ℕ} (l : RationalSegmentLottery n k) (f : RationalAffineAllocation n m) :
    (l.mapped f).real = l.real.mapped f.real := by
  apply SegmentLottery.eq_of_fields
  · rfl
  · funext slot
    exact f.value_real (l.P slot)
  · funext slot
    exact f.value_real (l.Q slot)

theorem mapped_law {n m k : ℕ} (l : RationalSegmentLottery n k) (f : RationalAffineAllocation n m) :
    (l.mapped f).real.law = l.real.law.map f.real.value := by
  rw [l.mapped_real]
  apply ProbabilityMeasure.toMeasure_injective
  exact l.real.mapped_law f.real

theorem mapped_point_real {n m k : ℕ} (l : RationalSegmentLottery n k) (f : RationalAffineAllocation n m)
    (K : ℕ) (slot : Fin k) (bits : Fin K → Bool) :
    (fun j => ((l.mapped f).point K slot bits j : ℝ)) = f.real.value (l.real.dyadicPoint K slot bits) := by
  rw [point_real, l.mapped_real]
  exact (f.real.onSegment (l.real.P slot) (l.real.Q slot) (dyadicMidpointSample K bits)).symm

end RationalSegmentLottery
end Blotto
