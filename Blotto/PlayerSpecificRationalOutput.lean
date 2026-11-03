import Blotto.PlayerSpecificFiniteAccuracyError

/-! Actual rational arrays are emitted by independently rounding each
computed algebraic coordinate downward. Nonnegative hard at-most budgets
hold on every bit path; original zero coordinates are preserved exactly. -/
namespace Blotto.PlayerSpecificRationalOutput
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run {N : ℕ} (root : Candidate) (y : FixedArrayTable N Data) (P : ℕ) : FixedArrayTable N ℚ :=
  FixedArrayTable.ofFn (fun j => PlayerSpecificAlgebraicOutputFloor.round root (y.read j) P)

noncomputable def allocation {N : ℕ} (y : FixedArrayTable N ℚ) : Allocation N := fun j => (y.read j:ℝ)

theorem coordinate_interval {N : ℕ} (y : FixedArrayTable N Data) (x B : ℝ)
    (hy : FullBudget B (PlayerSpecificAlgebraicSegment.values y x)) (hB : B ≤ 1) (j : Fin N) :
    0 ≤ realEvaluate (y.read j) x ∧ realEvaluate (y.read j) x ≤ 1 := by
  have hj : PlayerSpecificAlgebraicSegment.values y x j ≤ ∑ k,PlayerSpecificAlgebraicSegment.values y x k :=
    Finset.single_le_sum (fun k _ => hy.1 k) (Finset.mem_univ j)
  exact ⟨hy.1 j,hj.trans (hy.2.le.trans hB)⟩

theorem every_path {N : ℕ} (root : Candidate) (y : FixedArrayTable N Data) (P : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x B : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (hy : FullBudget B (PlayerSpecificAlgebraicSegment.values y x)) (hB : B ≤ 1) :
    Blotto.Feasible B (allocation (run root y P)) ∧
      ∀ j,allocation (run root y P) j ≤ realEvaluate (y.read j) x ∧
        realEvaluate (y.read j) x-allocation (run root y P) j < 1/(2:ℝ)^P ∧
        RationalHeight ((run root y P).read j) (P+2) := by
  have hbounds : ∀ j,0 ≤ allocation (run root y P) j ∧
      allocation (run root y P) j ≤ realEvaluate (y.read j) x ∧
      realEvaluate (y.read j) x-allocation (run root y P) j < 1/(2:ℝ)^P := by
    intro j
    simp only [allocation,run,FixedArrayTable.read_ofFn]
    exact PlayerSpecificAlgebraicOutputFloorBounds.round_bounds root (y.read j) P hm hirr hv x hx (coordinate_interval y x B hy hB j)
  refine ⟨⟨fun j => (hbounds j).1,?_⟩,?_⟩
  · exact (Finset.sum_le_sum (fun j _ => (hbounds j).2.1)).trans hy.2.le
  · intro j
    refine ⟨(hbounds j).2.1,(hbounds j).2.2,?_⟩
    simp only [run,FixedArrayTable.read_ofFn]
    exact PlayerSpecificAlgebraicOutputFloorSpecification.height root (y.read j) P hm hirr hv x hx (coordinate_interval y x B hy hB j)

theorem zero {N : ℕ} (root : Candidate) (y : FixedArrayTable N Data) (P : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (j : Fin N) (hj : realEvaluate (y.read j) x=0) : (run root y P).read j=0 := by
  rw [run,FixedArrayTable.read_ofFn]
  exact PlayerSpecificAlgebraicOutputFloorBounds.zero root (y.read j) P hm hirr hv x hx hj

theorem comparisons {N : ℕ} (root : Candidate) (y : FixedArrayTable N Data) (P : ℕ) :
    (∑ j,(PlayerSpecificAlgebraicOutputFloor.search root (y.read j) P).2) ≤ N*(P+2) := by
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => PlayerSpecificAlgebraicOutputFloorBounds.visits root (y.read j) P)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using h

end Blotto.PlayerSpecificRationalOutput
