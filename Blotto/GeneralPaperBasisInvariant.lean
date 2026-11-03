import Blotto.GeneralPaperBasisState

/-! The basis invariant records actual original row provenance, the
nonsingular leading minor and native cache, and feasibility of the
freshly recomputed rational point. All proofs are erased from execution.
-/
namespace Blotto.GeneralPaperBasisInvariant
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperStrictScore
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisState
open GeneralPaperBasisCoordinates GeneralPaperBasisOriginalDirection GeneralPaperBasisFreshPointSound
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Invariant {T m K j : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1))) (hj : j≤m*(K-1)) (state : State j (m*(K-1))) : Prop where
  nonzero : state.determinant≠0
  cache : GeneralPaperBasisStoredCorrect.Valid state.determinant state.adjugate (minor state.rows hj)
  original : ∀ i,∃ r : Index T m K (score v S) h,
    state.rows.read i=GeneralPaperBasisDenseRow.build (constraints dict.label (score v S) h r)
  feasible : GeneralPaperAffineConstraintRows.Feasible dict.label (score v S) h ((betaN:ℝ)/(N:ℝ))
    (fun a => values N betaN state.determinant state.adjugate state.rows initialGrid (index a))

theorem initial_point {d : ℕ} (N : ℕ) (betaN : ℤ) (initialGrid : Vector d) (k : Fin d) :
    values N betaN (initial d).determinant (initial d).adjugate (initial d).rows initialGrid k=
      (initialGrid.read k:ℝ)/(N:ℝ) := by
  simp only [values,GeneralPaperBasisFreshPoint.later_read N betaN (initial d).determinant
    (initial d).adjugate (initial d).rows initialGrid k (Nat.zero_le _),Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]

theorem initial_valid {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1)))
    (hStart : GeneralPaperAffineConstraintRows.Feasible dict.label (score v S) h ((betaN:ℝ)/(N:ℝ))
      (fun a => (initialGrid.read (index a):ℝ)/(N:ℝ))) :
    Invariant dict v S h N betaN initialGrid (Nat.zero_le _) (initial (m*(K-1))) := by
  refine ⟨by change (1:ℤ)≠0; norm_num,GeneralPaperBasisStoredCorrect.initial_valid _,?_,?_⟩
  · intro i
    exact Fin.elim0 i
  · simpa only [initial_point] using hStart

end Blotto.GeneralPaperBasisInvariant
